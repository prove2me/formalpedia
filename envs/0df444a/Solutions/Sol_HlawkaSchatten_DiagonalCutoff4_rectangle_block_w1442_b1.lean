-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1442_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:57:22.988443+00:00
-- url     : https://prove2.me/submissions/b5d8eddd-524b-4b30-9bd6-6f22740dc49b

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
theorem support_rectangle_w1442_s3_0 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-979824939/5000000000 : ℝ)*x 0 + (135399791/250000000 : ℝ)*x 1 + (32746211/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (979824939/5000000000 : ℝ)^2201 ≤ (11956688657089/100000000000000 : ℝ)^1689 := by
    have hnat : (979824939 : ℕ)^2201*100000000000000^1689 ≤ 11956688657089^1689*5000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      979824939 5000000000 11956688657089 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135399791/250000000 : ℝ)^2201 ≤ (11243089918567/25000000000000 : ℝ)^1689 := by
    have hnat : (135399791 : ℕ)^2201*25000000000000^1689 ≤ 11243089918567^1689*250000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135399791 250000000 11243089918567 25000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32746211/62500000 : ℝ)^2201 ≤ (21535475826651/50000000000000 : ℝ)^1689 := by
    have hnat : (32746211 : ℕ)^2201*50000000000000^1689 ≤ 21535475826651^1689*62500000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32746211 62500000 21535475826651 50000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-979824939/5000000000 : ℝ), (135399791/250000000 : ℝ), (32746211/62500000 : ℝ)] ![(11956688657089/100000000000000 : ℝ), (11243089918567/25000000000000 : ℝ), (21535475826651/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-979824939/5000000000 : ℝ)|^2201 ≤ (11956688657089/100000000000000 : ℝ)^1689
        have hw : |(-979824939/5000000000 : ℝ)|=(979824939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(135399791/250000000 : ℝ)|^2201 ≤ (11243089918567/25000000000000 : ℝ)^1689
        have hw : |(135399791/250000000 : ℝ)|=(135399791/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(32746211/62500000 : ℝ)|^2201 ≤ (21535475826651/50000000000000 : ℝ)^1689
        have hw : |(32746211/62500000 : ℝ)|=(32746211/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s3_1 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349234673/10000000000 : ℝ)*x 0 + (-2049711209/10000000000 : ℝ)*x 1 + (2619696553/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349234673/10000000000 : ℝ)^2201 ≤ (22125675722041/50000000000000 : ℝ)^1689 := by
    have hnat : (5349234673 : ℕ)^2201*50000000000000^1689 ≤ 22125675722041^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349234673 10000000000 22125675722041 50000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2049711209/10000000000 : ℝ)^2201 ≤ (3169425973307/25000000000000 : ℝ)^1689 := by
    have hnat : (2049711209 : ℕ)^2201*25000000000000^1689 ≤ 3169425973307^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049711209 10000000000 3169425973307 25000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2619696553/5000000000 : ℝ)^2201 ≤ (43070944647279/100000000000000 : ℝ)^1689 := by
    have hnat : (2619696553 : ℕ)^2201*100000000000000^1689 ≤ 43070944647279^1689*5000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619696553 5000000000 43070944647279 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349234673/10000000000 : ℝ), (-2049711209/10000000000 : ℝ), (2619696553/5000000000 : ℝ)] ![(22125675722041/50000000000000 : ℝ), (3169425973307/25000000000000 : ℝ), (43070944647279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349234673/10000000000 : ℝ)|^2201 ≤ (22125675722041/50000000000000 : ℝ)^1689
        have hw : |(5349234673/10000000000 : ℝ)|=(5349234673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2049711209/10000000000 : ℝ)|^2201 ≤ (3169425973307/25000000000000 : ℝ)^1689
        have hw : |(-2049711209/10000000000 : ℝ)|=(2049711209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2619696553/5000000000 : ℝ)|^2201 ≤ (43070944647279/100000000000000 : ℝ)^1689
        have hw : |(2619696553/5000000000 : ℝ)|=(2619696553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s3_2 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1069846923/2000000000 : ℝ)*x 0 + (1309848309/2500000000 : ℝ)*x 1 + (-1024855557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069846923/2000000000 : ℝ)^2201 ≤ (44251350818833/100000000000000 : ℝ)^1689 := by
    have hnat : (1069846923 : ℕ)^2201*100000000000000^1689 ≤ 44251350818833^1689*2000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069846923 2000000000 44251350818833 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1309848309/2500000000 : ℝ)^2201 ≤ (43070946039913/100000000000000 : ℝ)^1689 := by
    have hnat : (1309848309 : ℕ)^2201*100000000000000^1689 ≤ 43070946039913^1689*2500000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309848309 2500000000 43070946039913 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1024855557/5000000000 : ℝ)^2201 ≤ (6338851563761/50000000000000 : ℝ)^1689 := by
    have hnat : (1024855557 : ℕ)^2201*50000000000000^1689 ≤ 6338851563761^1689*5000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024855557 5000000000 6338851563761 50000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069846923/2000000000 : ℝ), (1309848309/2500000000 : ℝ), (-1024855557/5000000000 : ℝ)] ![(44251350818833/100000000000000 : ℝ), (43070946039913/100000000000000 : ℝ), (6338851563761/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069846923/2000000000 : ℝ)|^2201 ≤ (44251350818833/100000000000000 : ℝ)^1689
        have hw : |(1069846923/2000000000 : ℝ)|=(1069846923/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1309848309/2500000000 : ℝ)|^2201 ≤ (43070946039913/100000000000000 : ℝ)^1689
        have hw : |(1309848309/2500000000 : ℝ)|=(1309848309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1024855557/5000000000 : ℝ)|^2201 ≤ (6338851563761/50000000000000 : ℝ)^1689
        have hw : |(-1024855557/5000000000 : ℝ)|=(1024855557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s3_3 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4300533599/10000000000 : ℝ)*x 0 + (4112433177/10000000000 : ℝ)*x 1 + (562036759/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4300533599/10000000000 : ℝ)^2201 ≤ (16649418267569/50000000000000 : ℝ)^1689 := by
    have hnat : (4300533599 : ℕ)^2201*50000000000000^1689 ≤ 16649418267569^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4300533599 10000000000 16649418267569 50000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4112433177/10000000000 : ℝ)^2201 ≤ (31413590012701/100000000000000 : ℝ)^1689 := by
    have hnat : (4112433177 : ℕ)^2201*100000000000000^1689 ≤ 31413590012701^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4112433177 10000000000 31413590012701 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562036759/1250000000 : ℝ)^2201 ≤ (35287573438453/100000000000000 : ℝ)^1689 := by
    have hnat : (562036759 : ℕ)^2201*100000000000000^1689 ≤ 35287573438453^1689*1250000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562036759 1250000000 35287573438453 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4300533599/10000000000 : ℝ), (4112433177/10000000000 : ℝ), (562036759/1250000000 : ℝ)] ![(16649418267569/50000000000000 : ℝ), (31413590012701/100000000000000 : ℝ), (35287573438453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4300533599/10000000000 : ℝ)|^2201 ≤ (16649418267569/50000000000000 : ℝ)^1689
        have hw : |(4300533599/10000000000 : ℝ)|=(4300533599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4112433177/10000000000 : ℝ)|^2201 ≤ (31413590012701/100000000000000 : ℝ)^1689
        have hw : |(4112433177/10000000000 : ℝ)|=(4112433177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(562036759/1250000000 : ℝ)|^2201 ≤ (35287573438453/100000000000000 : ℝ)^1689
        have hw : |(562036759/1250000000 : ℝ)|=(562036759/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s3_4 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-391932899/2000000000 : ℝ)*x 0 + (5240095477/10000000000 : ℝ)*x 1 + (541528617/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (391932899/2000000000 : ℝ)^2201 ≤ (478272195091/4000000000000 : ℝ)^1689 := by
    have hnat : (391932899 : ℕ)^2201*4000000000000^1689 ≤ 478272195091^1689*2000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      391932899 2000000000 478272195091 4000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5240095477/10000000000 : ℝ)^2201 ≤ (43078469000961/100000000000000 : ℝ)^1689 := by
    have hnat : (5240095477 : ℕ)^2201*100000000000000^1689 ≤ 43078469000961^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240095477 10000000000 43078469000961 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541528617/1000000000 : ℝ)^2201 ≤ (44964726097831/100000000000000 : ℝ)^1689 := by
    have hnat : (541528617 : ℕ)^2201*100000000000000^1689 ≤ 44964726097831^1689*1000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541528617 1000000000 44964726097831 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-391932899/2000000000 : ℝ), (5240095477/10000000000 : ℝ), (541528617/1000000000 : ℝ)] ![(478272195091/4000000000000 : ℝ), (43078469000961/100000000000000 : ℝ), (44964726097831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-391932899/2000000000 : ℝ)|^2201 ≤ (478272195091/4000000000000 : ℝ)^1689
        have hw : |(-391932899/2000000000 : ℝ)|=(391932899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5240095477/10000000000 : ℝ)|^2201 ≤ (43078469000961/100000000000000 : ℝ)^1689
        have hw : |(5240095477/10000000000 : ℝ)|=(5240095477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541528617/1000000000 : ℝ)|^2201 ≤ (44964726097831/100000000000000 : ℝ)^1689
        have hw : |(541528617/1000000000 : ℝ)|=(541528617/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s3_5 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1325816617/2500000000 : ℝ)*x 0 + (-1873818733/10000000000 : ℝ)*x 1 + (1083057223/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325816617/2500000000 : ℝ)^2201 ≤ (43756453492719/100000000000000 : ℝ)^1689 := by
    have hnat : (1325816617 : ℕ)^2201*100000000000000^1689 ≤ 43756453492719^1689*2500000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325816617 2500000000 43756453492719 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1873818733/10000000000 : ℝ)^2201 ≤ (11278820986331/100000000000000 : ℝ)^1689 := by
    have hnat : (1873818733 : ℕ)^2201*100000000000000^1689 ≤ 11278820986331^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1873818733 10000000000 11278820986331 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083057223/2000000000 : ℝ)^2201 ≤ (5620590687839/12500000000000 : ℝ)^1689 := by
    have hnat : (1083057223 : ℕ)^2201*12500000000000^1689 ≤ 5620590687839^1689*2000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083057223 2000000000 5620590687839 12500000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325816617/2500000000 : ℝ), (-1873818733/10000000000 : ℝ), (1083057223/2000000000 : ℝ)] ![(43756453492719/100000000000000 : ℝ), (11278820986331/100000000000000 : ℝ), (5620590687839/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325816617/2500000000 : ℝ)|^2201 ≤ (43756453492719/100000000000000 : ℝ)^1689
        have hw : |(1325816617/2500000000 : ℝ)|=(1325816617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1873818733/10000000000 : ℝ)|^2201 ≤ (11278820986331/100000000000000 : ℝ)^1689
        have hw : |(-1873818733/10000000000 : ℝ)|=(1873818733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083057223/2000000000 : ℝ)|^2201 ≤ (5620590687839/12500000000000 : ℝ)^1689
        have hw : |(1083057223/2000000000 : ℝ)|=(1083057223/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s3_6 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2651632597/5000000000 : ℝ)*x 0 + (338455447/625000000 : ℝ)*x 1 + (-1873819049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651632597/5000000000 : ℝ)^2201 ≤ (21878219897339/50000000000000 : ℝ)^1689 := by
    have hnat : (2651632597 : ℕ)^2201*50000000000000^1689 ≤ 21878219897339^1689*5000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651632597 5000000000 21878219897339 50000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338455447/625000000 : ℝ)^2201 ≤ (22482368361703/50000000000000 : ℝ)^1689 := by
    have hnat : (338455447 : ℕ)^2201*50000000000000^1689 ≤ 22482368361703^1689*625000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338455447 625000000 22482368361703 50000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1873819049/10000000000 : ℝ)^2201 ≤ (2819705866243/25000000000000 : ℝ)^1689 := by
    have hnat : (1873819049 : ℕ)^2201*25000000000000^1689 ≤ 2819705866243^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1873819049 10000000000 2819705866243 25000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651632597/5000000000 : ℝ), (338455447/625000000 : ℝ), (-1873819049/10000000000 : ℝ)] ![(21878219897339/50000000000000 : ℝ), (22482368361703/50000000000000 : ℝ), (2819705866243/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651632597/5000000000 : ℝ)|^2201 ≤ (21878219897339/50000000000000 : ℝ)^1689
        have hw : |(2651632597/5000000000 : ℝ)|=(2651632597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338455447/625000000 : ℝ)|^2201 ≤ (22482368361703/50000000000000 : ℝ)^1689
        have hw : |(338455447/625000000 : ℝ)|=(338455447/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1873819049/10000000000 : ℝ)|^2201 ≤ (2819705866243/25000000000000 : ℝ)^1689
        have hw : |(-1873819049/10000000000 : ℝ)|=(1873819049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s3_7 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4300565337/10000000000 : ℝ)*x 0 + (2247384651/5000000000 : ℝ)*x 1 + (4113967419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4300565337/10000000000 : ℝ)^2201 ≤ (33299156776297/100000000000000 : ℝ)^1689 := by
    have hnat : (4300565337 : ℕ)^2201*100000000000000^1689 ≤ 33299156776297^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4300565337 10000000000 33299156776297 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2247384651/5000000000 : ℝ)^2201 ≤ (1102249377689/3125000000000 : ℝ)^1689 := by
    have hnat : (2247384651 : ℕ)^2201*3125000000000^1689 ≤ 1102249377689^1689*5000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247384651 5000000000 1102249377689 3125000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4113967419/10000000000 : ℝ)^2201 ≤ (31428863124563/100000000000000 : ℝ)^1689 := by
    have hnat : (4113967419 : ℕ)^2201*100000000000000^1689 ≤ 31428863124563^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4113967419 10000000000 31428863124563 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4300565337/10000000000 : ℝ), (2247384651/5000000000 : ℝ), (4113967419/10000000000 : ℝ)] ![(33299156776297/100000000000000 : ℝ), (1102249377689/3125000000000 : ℝ), (31428863124563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4300565337/10000000000 : ℝ)|^2201 ≤ (33299156776297/100000000000000 : ℝ)^1689
        have hw : |(4300565337/10000000000 : ℝ)|=(4300565337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2247384651/5000000000 : ℝ)|^2201 ≤ (1102249377689/3125000000000 : ℝ)^1689
        have hw : |(2247384651/5000000000 : ℝ)|=(2247384651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4113967419/10000000000 : ℝ)|^2201 ≤ (31428863124563/100000000000000 : ℝ)^1689
        have hw : |(4113967419/10000000000 : ℝ)|=(4113967419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1442_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158682137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15761/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2609/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (14/125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (747/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15761/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2609/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15761/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2609/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15761/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2609/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15761/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2609/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15761/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2609/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15761/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2609/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (2609/25000 : ℝ) ^ (4401/1024 : ℝ) ≤ (3025346519413489/50000000000000000000 : ℝ) := by
    have hpowers : (2609/25000 : ℝ)^4401 ≤ (3025346519413489/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2609 : ℕ)^4401*50000000000000000000^1024 ≤ 3025346519413489^1024*25000^4401 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2609 25000 3025346519413489 50000000000000000000 4401 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2609/25000 : ℝ)) (X := (3025346519413489/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4401 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15761/100000 : ℝ) ^ (4401/1024 : ℝ) ≤ (4448813100885223/12500000000000000000 : ℝ) := by
    have hpowers : (15761/100000 : ℝ)^4401 ≤ (4448813100885223/12500000000000000000 : ℝ)^1024 := by
      have hnat : (15761 : ℕ)^4401*12500000000000000000^1024 ≤ 4448813100885223^1024*100000^4401 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15761 100000 4448813100885223 12500000000000000000 4401 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15761/100000 : ℝ)) (X := (4448813100885223/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4401 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003025346519413489/25000000000000000000 : ℝ) ≤ (2000056311038631/2000000000000000 : ℝ) ^ (4401/1024 : ℝ) := by
    have hpowers : (25003025346519413489/25000000000000000000 : ℝ)^1024 ≤ (2000056311038631/2000000000000000 : ℝ)^4401 := by
      have hnat : (25003025346519413489 : ℕ)^1024*2000000000000000^4401 ≤ 2000056311038631^4401*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003025346519413489 25000000000000000000 2000056311038631 2000000000000000 1024 4401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000056311038631/2000000000000000 : ℝ)) (X := (25003025346519413489/25000000000000000000 : ℝ)) (by norm_num) 4401 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020820598922954381/50000000000000000000 : ℝ) ≤ (400038749171487/400000000000000 : ℝ) ^ (4401/1024 : ℝ) := by
    have hpowers : (50020820598922954381/50000000000000000000 : ℝ)^1024 ≤ (400038749171487/400000000000000 : ℝ)^4401 := by
      have hnat : (50020820598922954381 : ℕ)^1024*400000000000000^4401 ≤ 400038749171487^4401*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020820598922954381 50000000000000000000 400038749171487 400000000000000 1024 4401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400038749171487/400000000000000 : ℝ)) (X := (50020820598922954381/50000000000000000000 : ℝ)) (by norm_num) 4401 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254448813100885223/6250000000000000000 : ℝ) ≤ (2000331180676239/2000000000000000 : ℝ) ^ (4401/1024 : ℝ) := by
    have hpowers : (6254448813100885223/6250000000000000000 : ℝ)^1024 ≤ (2000331180676239/2000000000000000 : ℝ)^4401 := by
      have hnat : (6254448813100885223 : ℕ)^1024*2000000000000000^4401 ≤ 2000331180676239^4401*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254448813100885223 6250000000000000000 2000331180676239 2000000000000000 1024 4401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000331180676239/2000000000000000 : ℝ)) (X := (6254448813100885223/6250000000000000000 : ℝ)) (by norm_num) 4401 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3025346519413489/50000000000000000000 : ℝ) ≤ ((3549143772247544329/3550000000000000000 : ℝ)+2*(11452901567/8875000000000 : ℝ)*(2609/25000 : ℝ))^(4401/1024 : ℝ) := by
    rw [show (3549143772247544329/3550000000000000000 : ℝ)+2*(11452901567/8875000000000 : ℝ)*(2609/25000 : ℝ)=(2000056311038631/2000000000000000 : ℝ) by norm_num, show 1+2*(3025346519413489/50000000000000000000 : ℝ)=(25003025346519413489/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4448813100885223/12500000000000000000 : ℝ)+(3025346519413489/50000000000000000000 : ℝ) ≤ ((3549143772247544329/3550000000000000000 : ℝ)+(11452901567/8875000000000 : ℝ)*((15761/100000 : ℝ)+(2609/25000 : ℝ)))^(4401/1024 : ℝ) := by
    rw [show (3549143772247544329/3550000000000000000 : ℝ)+(11452901567/8875000000000 : ℝ)*((15761/100000 : ℝ)+(2609/25000 : ℝ))=(400038749171487/400000000000000 : ℝ) by norm_num, show 1+(4448813100885223/12500000000000000000 : ℝ)+(3025346519413489/50000000000000000000 : ℝ)=(50020820598922954381/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4448813100885223/12500000000000000000 : ℝ) ≤ ((3549143772247544329/3550000000000000000 : ℝ)+2*(11452901567/8875000000000 : ℝ)*(15761/100000 : ℝ))^(4401/1024 : ℝ) := by
    rw [show (3549143772247544329/3550000000000000000 : ℝ)+2*(11452901567/8875000000000 : ℝ)*(15761/100000 : ℝ)=(2000331180676239/2000000000000000 : ℝ) by norm_num, show 1+2*(4448813100885223/12500000000000000000 : ℝ)=(6254448813100885223/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3549143772247544329/3550000000000000000 : ℝ)*(X 1 0+X 2 0)+(11452901567/8875000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4401/1024 : ℝ)) (lo := (2609/25000 : ℝ)) (hi := (15761/100000 : ℝ)) (c := (3549143772247544329/3550000000000000000 : ℝ)) (alpha := (11452901567/8875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3549143772247544329/3550000000000000000 : ℝ)*(X 0 1+X 2 1)+(11452901567/8875000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4401/1024 : ℝ)) (lo := (2609/25000 : ℝ)) (hi := (15761/100000 : ℝ)) (c := (3549143772247544329/3550000000000000000 : ℝ)) (alpha := (11452901567/8875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3549143772247544329/3550000000000000000 : ℝ)*(X 0 2+X 1 2)+(11452901567/8875000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4401/1024 : ℝ)) (lo := (2609/25000 : ℝ)) (hi := (15761/100000 : ℝ)) (c := (3549143772247544329/3550000000000000000 : ℝ)) (alpha := (11452901567/8875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-979824939/5000000000 : ℝ)*X 0 0+(135399791/250000000 : ℝ)*X 0 1+(32746211/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349234673/10000000000 : ℝ)*X 1 0+(-2049711209/10000000000 : ℝ)*X 1 1+(2619696553/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069846923/2000000000 : ℝ)*X 2 0+(1309848309/2500000000 : ℝ)*X 2 1+(-1024855557/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4300533599/10000000000 : ℝ)*X 0 0+(4112433177/10000000000 : ℝ)*X 0 1+(562036759/1250000000 : ℝ)*X 0 2+(4300533599/10000000000 : ℝ)*X 1 0+(4112433177/10000000000 : ℝ)*X 1 1+(562036759/1250000000 : ℝ)*X 1 2+(4300533599/10000000000 : ℝ)*X 2 0+(4112433177/10000000000 : ℝ)*X 2 1+(562036759/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-391932899/2000000000 : ℝ)*X 0 0+(5240095477/10000000000 : ℝ)*X 0 1+(541528617/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1325816617/2500000000 : ℝ)*X 1 0+(-1873818733/10000000000 : ℝ)*X 1 1+(1083057223/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2651632597/5000000000 : ℝ)*X 2 0+(338455447/625000000 : ℝ)*X 2 1+(-1873819049/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4300565337/10000000000 : ℝ)*X 0 0+(2247384651/5000000000 : ℝ)*X 0 1+(4113967419/10000000000 : ℝ)*X 0 2+(4300565337/10000000000 : ℝ)*X 1 0+(2247384651/5000000000 : ℝ)*X 1 1+(4113967419/10000000000 : ℝ)*X 1 2+(4300565337/10000000000 : ℝ)*X 2 0+(2247384651/5000000000 : ℝ)*X 2 1+(4113967419/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (557528556887633383222586229/88750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (32189207/3125000000000 : ℝ)*(base19) + (87652451/10000000000000 : ℝ)*(base23) + (49283829/100000000000000 : ℝ)*(lower2) + (9703679/100000000000000 : ℝ)*(upper3) + (21466879/50000000000000 : ℝ)*(upper5) + (2066927419553211/50000000000000 : ℝ)*(major0) + (2066927419553211/50000000000000 : ℝ)*(major1) + (2066927419553211/50000000000000 : ℝ)*(major2) + (5662586503590483/100000000000000 : ℝ)*(sp0) + (2831295873096229/50000000000000 : ℝ)*(sp1) + (1415647974930643/25000000000000 : ℝ)*(sp2) + (1302556831797669/50000000000000 : ℝ)*(sp3) + (6272656599/100000000000000 : ℝ)*(sp4) + (605794003/20000000000000 : ℝ)*(sp7) + (325639586570669/12500000000000 : ℝ)*(f.failure) + (2831296388123541/50000000000000 : ℝ)*(f.sum) + (516404331573/887500000000000000000000000 : ℝ)*base65 + (289501362929090419/177500000000000000000000000000000 : ℝ)*base67 + (1445465438999090419/177500000000000000000000000000000 : ℝ)*base69 + (321015679949090419/177500000000000000000000000000000 : ℝ)*base71 + (5155500511127/887500000000000000000000000 : ℝ)*base74 + (2822000545754090419/177500000000000000000000000000000 : ℝ)*base75 + (2278035975534090419/177500000000000000000000000000000 : ℝ)*base77 + (1193392041481590419/177500000000000000000000000000000 : ℝ)*base79 + (1416060279979/1775000000000000000000000000 : ℝ)*base82 + (16560347/1250000000000000000000 : ℝ)*base90 + (16560347/1250000000000000000000 : ℝ)*base92 + (16560347/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (180157226280980484932954223/44375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (159385471/50000000000000 : ℝ)*(base8) + (66094187/6250000000000 : ℝ)*(base21) + (68363589/50000000000000 : ℝ)*(base29) + (230430047/100000000000000 : ℝ)*(upper2) + (4167052909242481/100000000000000 : ℝ)*(major0) + (2083526522984829/50000000000000 : ℝ)*(major1) + (2083526522984829/50000000000000 : ℝ)*(major2) + (151506379/10000000000000 : ℝ)*(sp0) + (668110679/12500000000000 : ℝ)*(sp1) + (2682685087/50000000000000 : ℝ)*(sp2) + (5708066230451091/100000000000000 : ℝ)*(sp4) + (5708062582673213/100000000000000 : ℝ)*(sp5) + (2854030752340739/50000000000000 : ℝ)*(sp6) + (164127368270257/6250000000000 : ℝ)*(sp7) + (164127368270257/6250000000000 : ℝ)*(f.failure) + (5708068064285823/100000000000000 : ℝ)*(f.sum) + (12933589126119/1775000000000000000000000000 : ℝ)*base65 + (3016149746113315259/177500000000000000000000000000000 : ℝ)*base68 + (2117454460255815259/177500000000000000000000000000000 : ℝ)*base70 + (2473953641728159751/355000000000000000000000000000000 : ℝ)*base72 + (3678142503799/1775000000000000000000000000 : ℝ)*base74 + (2403051984045115259/177500000000000000000000000000000 : ℝ)*base76 + (6948123961840249/355000000000000000000000000000000 : ℝ)*base77 + (1560769634942615259/177500000000000000000000000000000 : ℝ)*base80 + (1104584324453/221875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (5549209/625000000000000000000 : ℝ)*base89 + (11799209/625000000000000000000 : ℝ)*base91 + (11799209/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1442_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158682137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15761/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2609/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (14/125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (747/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1442_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1442_s4_0 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-78419599/400000000 : ℝ)*x 0 + (5408799431/10000000000 : ℝ)*x 1 + (5246032299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (78419599/400000000 : ℝ)^2201 ≤ (11963368718857/100000000000000 : ℝ)^1689 := by
    have hnat : (78419599 : ℕ)^2201*100000000000000^1689 ≤ 11963368718857^1689*400000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78419599 400000000 11963368718857 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408799431/10000000000 : ℝ)^2201 ≤ (70147734561/156250000000 : ℝ)^1689 := by
    have hnat : (5408799431 : ℕ)^2201*156250000000^1689 ≤ 70147734561^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408799431 10000000000 70147734561 156250000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246032299/10000000000 : ℝ)^2201 ≤ (43142081144867/100000000000000 : ℝ)^1689 := by
    have hnat : (5246032299 : ℕ)^2201*100000000000000^1689 ≤ 43142081144867^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246032299 10000000000 43142081144867 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-78419599/400000000 : ℝ), (5408799431/10000000000 : ℝ), (5246032299/10000000000 : ℝ)] ![(11963368718857/100000000000000 : ℝ), (70147734561/156250000000 : ℝ), (43142081144867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-78419599/400000000 : ℝ)|^2201 ≤ (11963368718857/100000000000000 : ℝ)^1689
        have hw : |(-78419599/400000000 : ℝ)|=(78419599/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408799431/10000000000 : ℝ)|^2201 ≤ (70147734561/156250000000 : ℝ)^1689
        have hw : |(5408799431/10000000000 : ℝ)|=(5408799431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246032299/10000000000 : ℝ)|^2201 ≤ (43142081144867/100000000000000 : ℝ)^1689
        have hw : |(5246032299/10000000000 : ℝ)|=(5246032299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s4_1 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336843583/2500000000 : ℝ)*x 0 + (-2043370429/10000000000 : ℝ)*x 1 + (655754041/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336843583/2500000000 : ℝ)^2201 ≤ (176925190897/400000000000 : ℝ)^1689 := by
    have hnat : (1336843583 : ℕ)^2201*400000000000^1689 ≤ 176925190897^1689*2500000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336843583 2500000000 176925190897 400000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2043370429/10000000000 : ℝ)^2201 ≤ (12626620800807/100000000000000 : ℝ)^1689 := by
    have hnat : (2043370429 : ℕ)^2201*100000000000000^1689 ≤ 12626620800807^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2043370429 10000000000 12626620800807 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655754041/1250000000 : ℝ)^2201 ≤ (43142081455651/100000000000000 : ℝ)^1689 := by
    have hnat : (655754041 : ℕ)^2201*100000000000000^1689 ≤ 43142081455651^1689*1250000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655754041 1250000000 43142081455651 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336843583/2500000000 : ℝ), (-2043370429/10000000000 : ℝ), (655754041/1250000000 : ℝ)] ![(176925190897/400000000000 : ℝ), (12626620800807/100000000000000 : ℝ), (43142081455651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336843583/2500000000 : ℝ)|^2201 ≤ (176925190897/400000000000 : ℝ)^1689
        have hw : |(1336843583/2500000000 : ℝ)|=(1336843583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2043370429/10000000000 : ℝ)|^2201 ≤ (12626620800807/100000000000000 : ℝ)^1689
        have hw : |(-2043370429/10000000000 : ℝ)|=(2043370429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655754041/1250000000 : ℝ)|^2201 ≤ (43142081455651/100000000000000 : ℝ)^1689
        have hw : |(655754041/1250000000 : ℝ)|=(655754041/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s4_2 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5347374347/10000000000 : ℝ)*x 0 + (5246032321/10000000000 : ℝ)*x 1 + (-2043370419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347374347/10000000000 : ℝ)^2201 ≤ (2764456117871/6250000000000 : ℝ)^1689 := by
    have hnat : (5347374347 : ℕ)^2201*6250000000000^1689 ≤ 2764456117871^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347374347 10000000000 2764456117871 6250000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246032321/10000000000 : ℝ)^2201 ≤ (8628416276127/20000000000000 : ℝ)^1689 := by
    have hnat : (5246032321 : ℕ)^2201*20000000000000^1689 ≤ 8628416276127^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246032321 10000000000 8628416276127 20000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2043370419/10000000000 : ℝ)^2201 ≤ (6313310360141/50000000000000 : ℝ)^1689 := by
    have hnat : (2043370419 : ℕ)^2201*50000000000000^1689 ≤ 6313310360141^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2043370419 10000000000 6313310360141 50000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347374347/10000000000 : ℝ), (5246032321/10000000000 : ℝ), (-2043370419/10000000000 : ℝ)] ![(2764456117871/6250000000000 : ℝ), (8628416276127/20000000000000 : ℝ), (6313310360141/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347374347/10000000000 : ℝ)|^2201 ≤ (2764456117871/6250000000000 : ℝ)^1689
        have hw : |(5347374347/10000000000 : ℝ)|=(5347374347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246032321/10000000000 : ℝ)|^2201 ≤ (8628416276127/20000000000000 : ℝ)^1689
        have hw : |(5246032321/10000000000 : ℝ)|=(5246032321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2043370419/10000000000 : ℝ)|^2201 ≤ (6313310360141/50000000000000 : ℝ)^1689
        have hw : |(-2043370419/10000000000 : ℝ)|=(2043370419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s4_3 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (215052403/500000000 : ℝ)*x 0 + (2063701521/5000000000 : ℝ)*x 1 + (896240089/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215052403/500000000 : ℝ)^2201 ≤ (33304027611759/100000000000000 : ℝ)^1689 := by
    have hnat : (215052403 : ℕ)^2201*100000000000000^1689 ≤ 33304027611759^1689*500000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215052403 500000000 33304027611759 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2063701521/5000000000 : ℝ)^2201 ≤ (31562686132293/100000000000000 : ℝ)^1689 := by
    have hnat : (2063701521 : ℕ)^2201*100000000000000^1689 ≤ 31562686132293^1689*5000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063701521 5000000000 31562686132293 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (896240089/2000000000 : ℝ)^2201 ≤ (35133286239511/100000000000000 : ℝ)^1689 := by
    have hnat : (896240089 : ℕ)^2201*100000000000000^1689 ≤ 35133286239511^1689*2000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896240089 2000000000 35133286239511 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215052403/500000000 : ℝ), (2063701521/5000000000 : ℝ), (896240089/2000000000 : ℝ)] ![(33304027611759/100000000000000 : ℝ), (31562686132293/100000000000000 : ℝ), (35133286239511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215052403/500000000 : ℝ)|^2201 ≤ (33304027611759/100000000000000 : ℝ)^1689
        have hw : |(215052403/500000000 : ℝ)|=(215052403/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2063701521/5000000000 : ℝ)|^2201 ≤ (31562686132293/100000000000000 : ℝ)^1689
        have hw : |(2063701521/5000000000 : ℝ)|=(2063701521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(896240089/2000000000 : ℝ)|^2201 ≤ (35133286239511/100000000000000 : ℝ)^1689
        have hw : |(896240089/2000000000 : ℝ)|=(896240089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s4_4 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1960501721/10000000000 : ℝ)*x 0 + (2623314403/5000000000 : ℝ)*x 1 + (676024971/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1960501721/10000000000 : ℝ)^2201 ≤ (5981731061877/50000000000000 : ℝ)^1689 := by
    have hnat : (1960501721 : ℕ)^2201*50000000000000^1689 ≤ 5981731061877^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1960501721 10000000000 5981731061877 50000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623314403/5000000000 : ℝ)^2201 ≤ (43148473833519/100000000000000 : ℝ)^1689 := by
    have hnat : (2623314403 : ℕ)^2201*100000000000000^1689 ≤ 43148473833519^1689*5000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623314403 5000000000 43148473833519 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676024971/1250000000 : ℝ)^2201 ≤ (11222016006797/25000000000000 : ℝ)^1689 := by
    have hnat : (676024971 : ℕ)^2201*25000000000000^1689 ≤ 11222016006797^1689*1250000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676024971 1250000000 11222016006797 25000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1960501721/10000000000 : ℝ), (2623314403/5000000000 : ℝ), (676024971/1250000000 : ℝ)] ![(5981731061877/50000000000000 : ℝ), (43148473833519/100000000000000 : ℝ), (11222016006797/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1960501721/10000000000 : ℝ)|^2201 ≤ (5981731061877/50000000000000 : ℝ)^1689
        have hw : |(-1960501721/10000000000 : ℝ)|=(1960501721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623314403/5000000000 : ℝ)|^2201 ≤ (43148473833519/100000000000000 : ℝ)^1689
        have hw : |(2623314403/5000000000 : ℝ)|=(2623314403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676024971/1250000000 : ℝ)|^2201 ≤ (11222016006797/25000000000000 : ℝ)^1689
        have hw : |(676024971/1250000000 : ℝ)|=(676024971/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s4_5 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305006161/10000000000 : ℝ)*x 0 + (-940601527/5000000000 : ℝ)*x 1 + (2704099869/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305006161/10000000000 : ℝ)^2201 ≤ (2735947474583/6250000000000 : ℝ)^1689 := by
    have hnat : (5305006161 : ℕ)^2201*6250000000000^1689 ≤ 2735947474583^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305006161 10000000000 2735947474583 6250000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (940601527/5000000000 : ℝ)^2201 ≤ (1417097086163/12500000000000 : ℝ)^1689 := by
    have hnat : (940601527 : ℕ)^2201*12500000000000^1689 ≤ 1417097086163^1689*5000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      940601527 5000000000 1417097086163 12500000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704099869/5000000000 : ℝ)^2201 ≤ (44888063702707/100000000000000 : ℝ)^1689 := by
    have hnat : (2704099869 : ℕ)^2201*100000000000000^1689 ≤ 44888063702707^1689*5000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704099869 5000000000 44888063702707 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305006161/10000000000 : ℝ), (-940601527/5000000000 : ℝ), (2704099869/5000000000 : ℝ)] ![(2735947474583/6250000000000 : ℝ), (1417097086163/12500000000000 : ℝ), (44888063702707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305006161/10000000000 : ℝ)|^2201 ≤ (2735947474583/6250000000000 : ℝ)^1689
        have hw : |(5305006161/10000000000 : ℝ)|=(5305006161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-940601527/5000000000 : ℝ)|^2201 ≤ (1417097086163/12500000000000 : ℝ)^1689
        have hw : |(-940601527/5000000000 : ℝ)|=(940601527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704099869/5000000000 : ℝ)|^2201 ≤ (44888063702707/100000000000000 : ℝ)^1689
        have hw : |(2704099869/5000000000 : ℝ)|=(2704099869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s4_6 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305006153/10000000000 : ℝ)*x 0 + (2704099883/5000000000 : ℝ)*x 1 + (-1881203027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305006153/10000000000 : ℝ)^2201 ≤ (5471894938413/12500000000000 : ℝ)^1689 := by
    have hnat : (5305006153 : ℕ)^2201*12500000000000^1689 ≤ 5471894938413^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305006153 10000000000 5471894938413 12500000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704099883/5000000000 : ℝ)^2201 ≤ (11222016001389/25000000000000 : ℝ)^1689 := by
    have hnat : (2704099883 : ℕ)^2201*25000000000000^1689 ≤ 11222016001389^1689*5000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704099883 5000000000 11222016001389 25000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1881203027/10000000000 : ℝ)^2201 ≤ (2834194119317/25000000000000 : ℝ)^1689 := by
    have hnat : (1881203027 : ℕ)^2201*25000000000000^1689 ≤ 2834194119317^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1881203027 10000000000 2834194119317 25000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305006153/10000000000 : ℝ), (2704099883/5000000000 : ℝ), (-1881203027/10000000000 : ℝ)] ![(5471894938413/12500000000000 : ℝ), (11222016001389/25000000000000 : ℝ), (2834194119317/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305006153/10000000000 : ℝ)|^2201 ≤ (5471894938413/12500000000000 : ℝ)^1689
        have hw : |(5305006153/10000000000 : ℝ)|=(5305006153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704099883/5000000000 : ℝ)|^2201 ≤ (11222016001389/25000000000000 : ℝ)^1689
        have hw : |(2704099883/5000000000 : ℝ)|=(2704099883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1881203027/10000000000 : ℝ)|^2201 ≤ (2834194119317/25000000000000 : ℝ)^1689
        have hw : |(-1881203027/10000000000 : ℝ)|=(1881203027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s4_7 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (537634193/1250000000 : ℝ)*x 0 + (895980771/2000000000 : ℝ)*x 1 + (2064353219/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537634193/1250000000 : ℝ)^2201 ≤ (4163035594799/12500000000000 : ℝ)^1689 := by
    have hnat : (537634193 : ℕ)^2201*12500000000000^1689 ≤ 4163035594799^1689*1250000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537634193 1250000000 4163035594799 12500000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (895980771/2000000000 : ℝ)^2201 ≤ (8780009955673/25000000000000 : ℝ)^1689 := by
    have hnat : (895980771 : ℕ)^2201*25000000000000^1689 ≤ 8780009955673^1689*2000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895980771 2000000000 8780009955673 25000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2064353219/5000000000 : ℝ)^2201 ≤ (7893918849783/25000000000000 : ℝ)^1689 := by
    have hnat : (2064353219 : ℕ)^2201*25000000000000^1689 ≤ 7893918849783^1689*5000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064353219 5000000000 7893918849783 25000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537634193/1250000000 : ℝ), (895980771/2000000000 : ℝ), (2064353219/5000000000 : ℝ)] ![(4163035594799/12500000000000 : ℝ), (8780009955673/25000000000000 : ℝ), (7893918849783/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537634193/1250000000 : ℝ)|^2201 ≤ (4163035594799/12500000000000 : ℝ)^1689
        have hw : |(537634193/1250000000 : ℝ)|=(537634193/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(895980771/2000000000 : ℝ)|^2201 ≤ (8780009955673/25000000000000 : ℝ)^1689
        have hw : |(895980771/2000000000 : ℝ)|=(895980771/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2064353219/5000000000 : ℝ)|^2201 ≤ (7893918849783/25000000000000 : ℝ)^1689
        have hw : |(2064353219/5000000000 : ℝ)|=(2064353219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1442_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158682137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (747/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (14/125 : ℝ)*pair X i i ≤ pair X i h) :
    (5671/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1479/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (747/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (14/125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (747/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (14/125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (747/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (14/125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (747/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (14/125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (747/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (14/125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (747/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (14/125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (14/125 : ℝ) ^ (4401/1024 : ℝ) ≤ (8197476741616029/100000000000000000000 : ℝ) := by
    have hpowers : (14/125 : ℝ)^4401 ≤ (8197476741616029/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14 : ℕ)^4401*100000000000000000000^1024 ≤ 8197476741616029^1024*125^4401 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14 125 8197476741616029 100000000000000000000 4401 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14/125 : ℝ)) (X := (8197476741616029/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4401 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (747/5000 : ℝ) ^ (4401/1024 : ℝ) ≤ (28280131548236903/100000000000000000000 : ℝ) := by
    have hpowers : (747/5000 : ℝ)^4401 ≤ (28280131548236903/100000000000000000000 : ℝ)^1024 := by
      have hnat : (747 : ℕ)^4401*100000000000000000000^1024 ≤ 28280131548236903^1024*5000^4401 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        747 5000 28280131548236903 100000000000000000000 4401 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (747/5000 : ℝ)) (X := (28280131548236903/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4401 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008197476741616029/50000000000000000000 : ℝ) ≤ (2500095361147773/2500000000000000 : ℝ) ^ (4401/1024 : ℝ) := by
    have hpowers : (50008197476741616029/50000000000000000000 : ℝ)^1024 ≤ (2500095361147773/2500000000000000 : ℝ)^4401 := by
      have hnat : (50008197476741616029 : ℕ)^1024*2500000000000000^4401 ≤ 2500095361147773^4401*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008197476741616029 50000000000000000000 2500095361147773 2500000000000000 1024 4401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500095361147773/2500000000000000 : ℝ)) (X := (50008197476741616029/50000000000000000000 : ℝ)) (by norm_num) 4401 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25009119402072463233/25000000000000000000 : ℝ) ≤ (625053038861071/625000000000000 : ℝ) ^ (4401/1024 : ℝ) := by
    have hpowers : (25009119402072463233/25000000000000000000 : ℝ)^1024 ≤ (625053038861071/625000000000000 : ℝ)^4401 := by
      have hnat : (25009119402072463233 : ℕ)^1024*625000000000000^4401 ≤ 625053038861071^4401*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009119402072463233 25000000000000000000 625053038861071 625000000000000 1024 4401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625053038861071/625000000000000 : ℝ)) (X := (25009119402072463233/25000000000000000000 : ℝ)) (by norm_num) 4401 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028280131548236903/50000000000000000000 : ℝ) ≤ (500065789948159/500000000000000 : ℝ) ^ (4401/1024 : ℝ) := by
    have hpowers : (50028280131548236903/50000000000000000000 : ℝ)^1024 ≤ (500065789948159/500000000000000 : ℝ)^4401 := by
      have hnat : (50028280131548236903 : ℕ)^1024*500000000000000^4401 ≤ 500065789948159^4401*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028280131548236903 50000000000000000000 500065789948159 500000000000000 1024 4401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500065789948159/500000000000000 : ℝ)) (X := (50028280131548236903/50000000000000000000 : ℝ)) (by norm_num) 4401 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8197476741616029/100000000000000000000 : ℝ) ≤ ((467387022922541231/467500000000000000 : ℝ)+2*(116794296511/93500000000000 : ℝ)*(14/125 : ℝ))^(4401/1024 : ℝ) := by
    rw [show (467387022922541231/467500000000000000 : ℝ)+2*(116794296511/93500000000000 : ℝ)*(14/125 : ℝ)=(2500095361147773/2500000000000000 : ℝ) by norm_num, show 1+2*(8197476741616029/100000000000000000000 : ℝ)=(50008197476741616029/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28280131548236903/100000000000000000000 : ℝ)+(8197476741616029/100000000000000000000 : ℝ) ≤ ((467387022922541231/467500000000000000 : ℝ)+(116794296511/93500000000000 : ℝ)*((747/5000 : ℝ)+(14/125 : ℝ)))^(4401/1024 : ℝ) := by
    rw [show (467387022922541231/467500000000000000 : ℝ)+(116794296511/93500000000000 : ℝ)*((747/5000 : ℝ)+(14/125 : ℝ))=(625053038861071/625000000000000 : ℝ) by norm_num, show 1+(28280131548236903/100000000000000000000 : ℝ)+(8197476741616029/100000000000000000000 : ℝ)=(25009119402072463233/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28280131548236903/100000000000000000000 : ℝ) ≤ ((467387022922541231/467500000000000000 : ℝ)+2*(116794296511/93500000000000 : ℝ)*(747/5000 : ℝ))^(4401/1024 : ℝ) := by
    rw [show (467387022922541231/467500000000000000 : ℝ)+2*(116794296511/93500000000000 : ℝ)*(747/5000 : ℝ)=(500065789948159/500000000000000 : ℝ) by norm_num, show 1+2*(28280131548236903/100000000000000000000 : ℝ)=(50028280131548236903/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (467387022922541231/467500000000000000 : ℝ)*(X 1 0+X 2 0)+(116794296511/93500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4401/1024 : ℝ)) (lo := (14/125 : ℝ)) (hi := (747/5000 : ℝ)) (c := (467387022922541231/467500000000000000 : ℝ)) (alpha := (116794296511/93500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (467387022922541231/467500000000000000 : ℝ)*(X 0 1+X 2 1)+(116794296511/93500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4401/1024 : ℝ)) (lo := (14/125 : ℝ)) (hi := (747/5000 : ℝ)) (c := (467387022922541231/467500000000000000 : ℝ)) (alpha := (116794296511/93500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (467387022922541231/467500000000000000 : ℝ)*(X 0 2+X 1 2)+(116794296511/93500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4401/1024 : ℝ)) (lo := (14/125 : ℝ)) (hi := (747/5000 : ℝ)) (c := (467387022922541231/467500000000000000 : ℝ)) (alpha := (116794296511/93500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-78419599/400000000 : ℝ)*X 0 0+(5408799431/10000000000 : ℝ)*X 0 1+(5246032299/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336843583/2500000000 : ℝ)*X 1 0+(-2043370429/10000000000 : ℝ)*X 1 1+(655754041/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347374347/10000000000 : ℝ)*X 2 0+(5246032321/10000000000 : ℝ)*X 2 1+(-2043370419/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((215052403/500000000 : ℝ)*X 0 0+(2063701521/5000000000 : ℝ)*X 0 1+(896240089/2000000000 : ℝ)*X 0 2+(215052403/500000000 : ℝ)*X 1 0+(2063701521/5000000000 : ℝ)*X 1 1+(896240089/2000000000 : ℝ)*X 1 2+(215052403/500000000 : ℝ)*X 2 0+(2063701521/5000000000 : ℝ)*X 2 1+(896240089/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1960501721/10000000000 : ℝ)*X 0 0+(2623314403/5000000000 : ℝ)*X 0 1+(676024971/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305006161/10000000000 : ℝ)*X 1 0+(-940601527/5000000000 : ℝ)*X 1 1+(2704099869/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305006153/10000000000 : ℝ)*X 2 0+(2704099883/5000000000 : ℝ)*X 2 1+(-1881203027/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((537634193/1250000000 : ℝ)*X 0 0+(895980771/2000000000 : ℝ)*X 0 1+(2064353219/5000000000 : ℝ)*X 0 2+(537634193/1250000000 : ℝ)*X 1 0+(895980771/2000000000 : ℝ)*X 1 1+(2064353219/5000000000 : ℝ)*X 1 2+(537634193/1250000000 : ℝ)*X 2 0+(895980771/2000000000 : ℝ)*X 2 1+(2064353219/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1515734511342547616661/425000000000000000000000000 : ℝ) := by norm_num
    linear_combination (617987631/100000000000000 : ℝ)*(base19) + (529425729/100000000000000 : ℝ)*(base23) + (28286513/50000000000000 : ℝ)*(lower2) + (2769647/3125000000000 : ℝ)*(upper3) + (13736401/50000000000000 : ℝ)*(upper5) + (4485131427668771/100000000000000 : ℝ)*(major0) + (4485131427668771/100000000000000 : ℝ)*(major1) + (4485131427668771/100000000000000 : ℝ)*(major2) + (6143761070299779/100000000000000 : ℝ)*(sp0) + (1535943550536337/25000000000000 : ℝ)*(sp1) + (24575097162829/400000000000 : ℝ)*(sp2) + (353310178109271/12500000000000 : ℝ)*(sp3) + (34374583/250000000000 : ℝ)*(sp4) + (6491449249/100000000000000 : ℝ)*(sp7) + (1413243958161709/50000000000000 : ℝ)*(f.failure) + (6143774820132979/100000000000000 : ℝ)*(f.sum) + (389424933899/106250000000000000000000000 : ℝ)*base65 + (17085344211499809/4250000000000000000000000000000 : ℝ)*base68 + (17219506405750191/4250000000000000000000000000000 : ℝ)*base69 + (16768001692499809/4250000000000000000000000000000 : ℝ)*base72 + (1020196137549/106250000000000000000000000 : ℝ)*base73 + (17059916258000191/4250000000000000000000000000000 : ℝ)*base75 + (620838398000191/4250000000000000000000000000000 : ℝ)*base77 + (72247123990749809/4250000000000000000000000000000 : ℝ)*base80 + (2963428774671/425000000000000000000000000 : ℝ)*base81 + (25692133/5000000000000000000000 : ℝ)*base89 + (25692133/5000000000000000000000 : ℝ)*base91 + (25692133/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (228466127273518985933124843/23375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1516521333/100000000000000 : ℝ)*(base19) + (211450941/12500000000000 : ℝ)*(base23) + (176710151/100000000000000 : ℝ)*(upper3) + (83829267/100000000000000 : ℝ)*(lower4) + (42577347/20000000000000 : ℝ)*(upper5) + (4518315500959449/100000000000000 : ℝ)*(major0) + (4518315500959449/100000000000000 : ℝ)*(major1) + (4518315500959449/100000000000000 : ℝ)*(major2) + (30174647/97656250000 : ℝ)*(sp1) + (17102236931/50000000000000 : ℝ)*(sp2) + (38682690418023/625000000000 : ℝ)*(sp4) + (6189198051523819/100000000000000 : ℝ)*(sp5) + (618919457080229/10000000000000 : ℝ)*(sp6) + (569480041847363/20000000000000 : ℝ)*(sp7) + (569480041847363/20000000000000 : ℝ)*(f.failure) + (38682690418023/625000000000 : ℝ)*(f.sum) + (344886766561/4675000000000000000000000000 : ℝ)*base66 + (293527511114986719/46750000000000000000000000000000 : ℝ)*base67 + (345214624106236719/46750000000000000000000000000000 : ℝ)*base69 + (67784542097486719/46750000000000000000000000000000 : ℝ)*base71 + (7708949762857/2337500000000000000000000000 : ℝ)*base73 + (313843798504263281/46750000000000000000000000000000 : ℝ)*base76 + (232079136283263281/46750000000000000000000000000000 : ℝ)*base78 + (128842606241486719/46750000000000000000000000000000 : ℝ)*base79 + (14559625764911/4675000000000000000000000000 : ℝ)*base82 + (8654731/2000000000000000000000 : ℝ)*base89 + (8654731/2000000000000000000000 : ℝ)*base91 + (8654731/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1442_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158682137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (747/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (14/125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5671/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1479/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1442_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1442_s5_0 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1960611361/10000000000 : ℝ)*x 0 + (1081541991/2000000000 : ℝ)*x 1 + (2623520889/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1960611361/10000000000 : ℝ)^2201 ≤ (11964333995797/100000000000000 : ℝ)^1689 := by
    have hnat : (1960611361 : ℕ)^2201*100000000000000^1689 ≤ 11964333995797^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1960611361 10000000000 11964333995797 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081541991/2000000000 : ℝ)^2201 ≤ (8976553251953/20000000000000 : ℝ)^1689 := by
    have hnat : (1081541991 : ℕ)^2201*20000000000000^1689 ≤ 8976553251953^1689*2000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081541991 2000000000 8976553251953 20000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623520889/5000000000 : ℝ)^2201 ≤ (21576449865149/50000000000000 : ℝ)^1689 := by
    have hnat : (2623520889 : ℕ)^2201*50000000000000^1689 ≤ 21576449865149^1689*5000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623520889 5000000000 21576449865149 50000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1960611361/10000000000 : ℝ), (1081541991/2000000000 : ℝ), (2623520889/5000000000 : ℝ)] ![(11964333995797/100000000000000 : ℝ), (8976553251953/20000000000000 : ℝ), (21576449865149/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1960611361/10000000000 : ℝ)|^2201 ≤ (11964333995797/100000000000000 : ℝ)^1689
        have hw : |(-1960611361/10000000000 : ℝ)|=(1960611361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081541991/2000000000 : ℝ)|^2201 ≤ (8976553251953/20000000000000 : ℝ)^1689
        have hw : |(1081541991/2000000000 : ℝ)|=(1081541991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623520889/5000000000 : ℝ)|^2201 ≤ (21576449865149/50000000000000 : ℝ)^1689
        have hw : |(2623520889/5000000000 : ℝ)|=(2623520889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s5_1 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5347092597/10000000000 : ℝ)*x 0 + (-1021202009/5000000000 : ℝ)*x 1 + (2623520889/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347092597/10000000000 : ℝ)^2201 ≤ (11057065229959/25000000000000 : ℝ)^1689 := by
    have hnat : (5347092597 : ℕ)^2201*25000000000000^1689 ≤ 11057065229959^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347092597 10000000000 11057065229959 25000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1021202009/5000000000 : ℝ)^2201 ≤ (6309419669817/50000000000000 : ℝ)^1689 := by
    have hnat : (1021202009 : ℕ)^2201*50000000000000^1689 ≤ 6309419669817^1689*5000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021202009 5000000000 6309419669817 50000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623520889/5000000000 : ℝ)^2201 ≤ (21576449865149/50000000000000 : ℝ)^1689 := by
    have hnat : (2623520889 : ℕ)^2201*50000000000000^1689 ≤ 21576449865149^1689*5000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623520889 5000000000 21576449865149 50000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347092597/10000000000 : ℝ), (-1021202009/5000000000 : ℝ), (2623520889/5000000000 : ℝ)] ![(11057065229959/25000000000000 : ℝ), (6309419669817/50000000000000 : ℝ), (21576449865149/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347092597/10000000000 : ℝ)|^2201 ≤ (11057065229959/25000000000000 : ℝ)^1689
        have hw : |(5347092597/10000000000 : ℝ)|=(5347092597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1021202009/5000000000 : ℝ)|^2201 ≤ (6309419669817/50000000000000 : ℝ)^1689
        have hw : |(-1021202009/5000000000 : ℝ)|=(1021202009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623520889/5000000000 : ℝ)|^2201 ≤ (21576449865149/50000000000000 : ℝ)^1689
        have hw : |(2623520889/5000000000 : ℝ)|=(2623520889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s5_2 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5347092597/10000000000 : ℝ)*x 0 + (2623520889/5000000000 : ℝ)*x 1 + (-1021202009/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347092597/10000000000 : ℝ)^2201 ≤ (11057065229959/25000000000000 : ℝ)^1689 := by
    have hnat : (5347092597 : ℕ)^2201*25000000000000^1689 ≤ 11057065229959^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347092597 10000000000 11057065229959 25000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623520889/5000000000 : ℝ)^2201 ≤ (21576449865149/50000000000000 : ℝ)^1689 := by
    have hnat : (2623520889 : ℕ)^2201*50000000000000^1689 ≤ 21576449865149^1689*5000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623520889 5000000000 21576449865149 50000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1021202009/5000000000 : ℝ)^2201 ≤ (6309419669817/50000000000000 : ℝ)^1689 := by
    have hnat : (1021202009 : ℕ)^2201*50000000000000^1689 ≤ 6309419669817^1689*5000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021202009 5000000000 6309419669817 50000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347092597/10000000000 : ℝ), (2623520889/5000000000 : ℝ), (-1021202009/5000000000 : ℝ)] ![(11057065229959/25000000000000 : ℝ), (21576449865149/50000000000000 : ℝ), (6309419669817/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347092597/10000000000 : ℝ)|^2201 ≤ (11057065229959/25000000000000 : ℝ)^1689
        have hw : |(5347092597/10000000000 : ℝ)|=(5347092597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623520889/5000000000 : ℝ)|^2201 ≤ (21576449865149/50000000000000 : ℝ)^1689
        have hw : |(2623520889/5000000000 : ℝ)|=(2623520889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1021202009/5000000000 : ℝ)|^2201 ≤ (6309419669817/50000000000000 : ℝ)^1689
        have hw : |(-1021202009/5000000000 : ℝ)|=(1021202009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s5_3 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4301122413/10000000000 : ℝ)*x 0 + (4129675211/10000000000 : ℝ)*x 1 + (4478910427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4301122413/10000000000 : ℝ)^2201 ≤ (33304777872963/100000000000000 : ℝ)^1689 := by
    have hnat : (4301122413 : ℕ)^2201*100000000000000^1689 ≤ 33304777872963^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4301122413 10000000000 33304777872963 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4129675211/10000000000 : ℝ)^2201 ≤ (31585330715491/100000000000000 : ℝ)^1689 := by
    have hnat : (4129675211 : ℕ)^2201*100000000000000^1689 ≤ 31585330715491^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4129675211 10000000000 31585330715491 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4478910427/10000000000 : ℝ)^2201 ≤ (35109891401169/100000000000000 : ℝ)^1689 := by
    have hnat : (4478910427 : ℕ)^2201*100000000000000^1689 ≤ 35109891401169^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478910427 10000000000 35109891401169 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4301122413/10000000000 : ℝ), (4129675211/10000000000 : ℝ), (4478910427/10000000000 : ℝ)] ![(33304777872963/100000000000000 : ℝ), (31585330715491/100000000000000 : ℝ), (35109891401169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4301122413/10000000000 : ℝ)|^2201 ≤ (33304777872963/100000000000000 : ℝ)^1689
        have hw : |(4301122413/10000000000 : ℝ)|=(4301122413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4129675211/10000000000 : ℝ)|^2201 ≤ (31585330715491/100000000000000 : ℝ)^1689
        have hw : |(4129675211/10000000000 : ℝ)|=(4129675211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4478910427/10000000000 : ℝ)|^2201 ≤ (35109891401169/100000000000000 : ℝ)^1689
        have hw : |(4478910427/10000000000 : ℝ)|=(4478910427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s5_4 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-15317363/78125000 : ℝ)*x 0 + (5247623309/10000000000 : ℝ)*x 1 + (2703562767/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (15317363/78125000 : ℝ)^2201 ≤ (2991105572293/25000000000000 : ℝ)^1689 := by
    have hnat : (15317363 : ℕ)^2201*25000000000000^1689 ≤ 2991105572293^1689*78125000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15317363 78125000 2991105572293 25000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247623309/10000000000 : ℝ)^2201 ≤ (43159132283883/100000000000000 : ℝ)^1689 := by
    have hnat : (5247623309 : ℕ)^2201*100000000000000^1689 ≤ 43159132283883^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247623309 10000000000 43159132283883 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703562767/5000000000 : ℝ)^2201 ≤ (22438222706093/50000000000000 : ℝ)^1689 := by
    have hnat : (2703562767 : ℕ)^2201*50000000000000^1689 ≤ 22438222706093^1689*5000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703562767 5000000000 22438222706093 50000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-15317363/78125000 : ℝ), (5247623309/10000000000 : ℝ), (2703562767/5000000000 : ℝ)] ![(2991105572293/25000000000000 : ℝ), (43159132283883/100000000000000 : ℝ), (22438222706093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-15317363/78125000 : ℝ)|^2201 ≤ (2991105572293/25000000000000 : ℝ)^1689
        have hw : |(-15317363/78125000 : ℝ)|=(15317363/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247623309/10000000000 : ℝ)|^2201 ≤ (43159132283883/100000000000000 : ℝ)^1689
        have hw : |(5247623309/10000000000 : ℝ)|=(5247623309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703562767/5000000000 : ℝ)|^2201 ≤ (22438222706093/50000000000000 : ℝ)^1689
        have hw : |(2703562767/5000000000 : ℝ)|=(2703562767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s5_5 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305270559/10000000000 : ℝ)*x 0 + (-1882320373/10000000000 : ℝ)*x 1 + (216285021/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305270559/10000000000 : ℝ)^2201 ≤ (2736125168967/6250000000000 : ℝ)^1689 := by
    have hnat : (5305270559 : ℕ)^2201*6250000000000^1689 ≤ 2736125168967^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305270559 10000000000 2736125168967 6250000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1882320373/10000000000 : ℝ)^2201 ≤ (2836387990307/25000000000000 : ℝ)^1689 := by
    have hnat : (1882320373 : ℕ)^2201*25000000000000^1689 ≤ 2836387990307^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1882320373 10000000000 2836387990307 25000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216285021/400000000 : ℝ)^2201 ≤ (44876445314847/100000000000000 : ℝ)^1689 := by
    have hnat : (216285021 : ℕ)^2201*100000000000000^1689 ≤ 44876445314847^1689*400000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216285021 400000000 44876445314847 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305270559/10000000000 : ℝ), (-1882320373/10000000000 : ℝ), (216285021/400000000 : ℝ)] ![(2736125168967/6250000000000 : ℝ), (2836387990307/25000000000000 : ℝ), (44876445314847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305270559/10000000000 : ℝ)|^2201 ≤ (2736125168967/6250000000000 : ℝ)^1689
        have hw : |(5305270559/10000000000 : ℝ)|=(5305270559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1882320373/10000000000 : ℝ)|^2201 ≤ (2836387990307/25000000000000 : ℝ)^1689
        have hw : |(-1882320373/10000000000 : ℝ)|=(1882320373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216285021/400000000 : ℝ)|^2201 ≤ (44876445314847/100000000000000 : ℝ)^1689
        have hw : |(216285021/400000000 : ℝ)|=(216285021/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s5_6 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652634971/5000000000 : ℝ)*x 0 + (5407126231/10000000000 : ℝ)*x 1 + (-941160123/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652634971/5000000000 : ℝ)^2201 ≤ (43777996068731/100000000000000 : ℝ)^1689 := by
    have hnat : (2652634971 : ℕ)^2201*100000000000000^1689 ≤ 43777996068731^1689*5000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652634971 5000000000 43777996068731 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407126231/10000000000 : ℝ)^2201 ≤ (11219113237629/25000000000000 : ℝ)^1689 := by
    have hnat : (5407126231 : ℕ)^2201*25000000000000^1689 ≤ 11219113237629^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407126231 10000000000 11219113237629 25000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (941160123/5000000000 : ℝ)^2201 ≤ (5672775481849/50000000000000 : ℝ)^1689 := by
    have hnat : (941160123 : ℕ)^2201*50000000000000^1689 ≤ 5672775481849^1689*5000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941160123 5000000000 5672775481849 50000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652634971/5000000000 : ℝ), (5407126231/10000000000 : ℝ), (-941160123/5000000000 : ℝ)] ![(43777996068731/100000000000000 : ℝ), (11219113237629/25000000000000 : ℝ), (5672775481849/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652634971/5000000000 : ℝ)|^2201 ≤ (43777996068731/100000000000000 : ℝ)^1689
        have hw : |(2652634971/5000000000 : ℝ)|=(2652634971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407126231/10000000000 : ℝ)|^2201 ≤ (11219113237629/25000000000000 : ℝ)^1689
        have hw : |(5407126231/10000000000 : ℝ)|=(5407126231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-941160123/5000000000 : ℝ)|^2201 ≤ (5672775481849/50000000000000 : ℝ)^1689
        have hw : |(-941160123/5000000000 : ℝ)|=(941160123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s5_7 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4301146853/10000000000 : ℝ)*x 0 + (895529437/2000000000 : ℝ)*x 1 + (4130945067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4301146853/10000000000 : ℝ)^2201 ≤ (2081564030399/6250000000000 : ℝ)^1689 := by
    have hnat : (4301146853 : ℕ)^2201*6250000000000^1689 ≤ 2081564030399^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4301146853 10000000000 2081564030399 6250000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (895529437/2000000000 : ℝ)^2201 ≤ (3509698766451/10000000000000 : ℝ)^1689 := by
    have hnat : (895529437 : ℕ)^2201*10000000000000^1689 ≤ 3509698766451^1689*2000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895529437 2000000000 3509698766451 10000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4130945067/10000000000 : ℝ)^2201 ≤ (31597987827961/100000000000000 : ℝ)^1689 := by
    have hnat : (4130945067 : ℕ)^2201*100000000000000^1689 ≤ 31597987827961^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4130945067 10000000000 31597987827961 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4301146853/10000000000 : ℝ), (895529437/2000000000 : ℝ), (4130945067/10000000000 : ℝ)] ![(2081564030399/6250000000000 : ℝ), (3509698766451/10000000000000 : ℝ), (31597987827961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4301146853/10000000000 : ℝ)|^2201 ≤ (2081564030399/6250000000000 : ℝ)^1689
        have hw : |(4301146853/10000000000 : ℝ)|=(4301146853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(895529437/2000000000 : ℝ)|^2201 ≤ (3509698766451/10000000000000 : ℝ)^1689
        have hw : |(895529437/2000000000 : ℝ)|=(895529437/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4130945067/10000000000 : ℝ)|^2201 ≤ (31597987827961/100000000000000 : ℝ)^1689
        have hw : |(4130945067/10000000000 : ℝ)|=(4130945067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1442_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158682137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1479/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5671/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11363/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14767/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1479/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5671/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1479/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5671/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1479/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5671/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1479/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5671/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1479/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5671/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1479/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5671/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5671/50000 : ℝ) ^ (4401/1024 : ℝ) ≤ (8653591794731677/100000000000000000000 : ℝ) := by
    have hpowers : (5671/50000 : ℝ)^4401 ≤ (8653591794731677/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5671 : ℕ)^4401*100000000000000000000^1024 ≤ 8653591794731677^1024*50000^4401 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5671 50000 8653591794731677 100000000000000000000 4401 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5671/50000 : ℝ)) (X := (8653591794731677/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4401 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1479/10000 : ℝ) ^ (4401/1024 : ℝ) ≤ (13539930153553731/50000000000000000000 : ℝ) := by
    have hpowers : (1479/10000 : ℝ)^4401 ≤ (13539930153553731/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1479 : ℕ)^4401*50000000000000000000^1024 ≤ 13539930153553731^1024*10000^4401 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1479 10000 13539930153553731 50000000000000000000 4401 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1479/10000 : ℝ)) (X := (13539930153553731/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4401 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008653591794731677/50000000000000000000 : ℝ) ≤ (10000402667105571/10000000000000000 : ℝ) ^ (4401/1024 : ℝ) := by
    have hpowers : (50008653591794731677/50000000000000000000 : ℝ)^1024 ≤ (10000402667105571/10000000000000000 : ℝ)^4401 := by
      have hnat : (50008653591794731677 : ℕ)^1024*10000000000000000^4401 ≤ 10000402667105571^4401*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008653591794731677 50000000000000000000 10000402667105571 10000000000000000 1024 4401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000402667105571/10000000000000000 : ℝ)) (X := (50008653591794731677/50000000000000000000 : ℝ)) (by norm_num) 4401 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100035733452101839139/100000000000000000000 : ℝ) ≤ (2500207827990923/2500000000000000 : ℝ) ^ (4401/1024 : ℝ) := by
    have hpowers : (100035733452101839139/100000000000000000000 : ℝ)^1024 ≤ (2500207827990923/2500000000000000 : ℝ)^4401 := by
      have hnat : (100035733452101839139 : ℕ)^1024*2500000000000000^4401 ≤ 2500207827990923^4401*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100035733452101839139 100000000000000000000 2500207827990923 2500000000000000 1024 4401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500207827990923/2500000000000000 : ℝ)) (X := (100035733452101839139/100000000000000000000 : ℝ)) (by norm_num) 4401 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013539930153553731/25000000000000000000 : ℝ) ≤ (10001259956821813/10000000000000000 : ℝ) ^ (4401/1024 : ℝ) := by
    have hpowers : (25013539930153553731/25000000000000000000 : ℝ)^1024 ≤ (10001259956821813/10000000000000000 : ℝ)^4401 := by
      have hnat : (25013539930153553731 : ℕ)^1024*10000000000000000^4401 ≤ 10001259956821813^4401*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013539930153553731 25000000000000000000 10001259956821813 10000000000000000 1024 4401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001259956821813/10000000000000000 : ℝ)) (X := (25013539930153553731/25000000000000000000 : ℝ)) (by norm_num) 4401 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8653591794731677/100000000000000000000 : ℝ) ≤ ((8617916254054598011/8620000000000000000 : ℝ)+2*(428644858121/344800000000000 : ℝ)*(5671/50000 : ℝ))^(4401/1024 : ℝ) := by
    rw [show (8617916254054598011/8620000000000000000 : ℝ)+2*(428644858121/344800000000000 : ℝ)*(5671/50000 : ℝ)=(10000402667105571/10000000000000000 : ℝ) by norm_num, show 1+2*(8653591794731677/100000000000000000000 : ℝ)=(50008653591794731677/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13539930153553731/50000000000000000000 : ℝ)+(8653591794731677/100000000000000000000 : ℝ) ≤ ((8617916254054598011/8620000000000000000 : ℝ)+(428644858121/344800000000000 : ℝ)*((1479/10000 : ℝ)+(5671/50000 : ℝ)))^(4401/1024 : ℝ) := by
    rw [show (8617916254054598011/8620000000000000000 : ℝ)+(428644858121/344800000000000 : ℝ)*((1479/10000 : ℝ)+(5671/50000 : ℝ))=(2500207827990923/2500000000000000 : ℝ) by norm_num, show 1+(13539930153553731/50000000000000000000 : ℝ)+(8653591794731677/100000000000000000000 : ℝ)=(100035733452101839139/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13539930153553731/50000000000000000000 : ℝ) ≤ ((8617916254054598011/8620000000000000000 : ℝ)+2*(428644858121/344800000000000 : ℝ)*(1479/10000 : ℝ))^(4401/1024 : ℝ) := by
    rw [show (8617916254054598011/8620000000000000000 : ℝ)+2*(428644858121/344800000000000 : ℝ)*(1479/10000 : ℝ)=(10001259956821813/10000000000000000 : ℝ) by norm_num, show 1+2*(13539930153553731/50000000000000000000 : ℝ)=(25013539930153553731/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8617916254054598011/8620000000000000000 : ℝ)*(X 1 0+X 2 0)+(428644858121/344800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4401/1024 : ℝ)) (lo := (5671/50000 : ℝ)) (hi := (1479/10000 : ℝ)) (c := (8617916254054598011/8620000000000000000 : ℝ)) (alpha := (428644858121/344800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8617916254054598011/8620000000000000000 : ℝ)*(X 0 1+X 2 1)+(428644858121/344800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4401/1024 : ℝ)) (lo := (5671/50000 : ℝ)) (hi := (1479/10000 : ℝ)) (c := (8617916254054598011/8620000000000000000 : ℝ)) (alpha := (428644858121/344800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8617916254054598011/8620000000000000000 : ℝ)*(X 0 2+X 1 2)+(428644858121/344800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4401/1024 : ℝ)) (lo := (5671/50000 : ℝ)) (hi := (1479/10000 : ℝ)) (c := (8617916254054598011/8620000000000000000 : ℝ)) (alpha := (428644858121/344800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1960611361/10000000000 : ℝ)*X 0 0+(1081541991/2000000000 : ℝ)*X 0 1+(2623520889/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347092597/10000000000 : ℝ)*X 1 0+(-1021202009/5000000000 : ℝ)*X 1 1+(2623520889/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347092597/10000000000 : ℝ)*X 2 0+(2623520889/5000000000 : ℝ)*X 2 1+(-1021202009/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4301122413/10000000000 : ℝ)*X 0 0+(4129675211/10000000000 : ℝ)*X 0 1+(4478910427/10000000000 : ℝ)*X 0 2+(4301122413/10000000000 : ℝ)*X 1 0+(4129675211/10000000000 : ℝ)*X 1 1+(4478910427/10000000000 : ℝ)*X 1 2+(4301122413/10000000000 : ℝ)*X 2 0+(4129675211/10000000000 : ℝ)*X 2 1+(4478910427/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-15317363/78125000 : ℝ)*X 0 0+(5247623309/10000000000 : ℝ)*X 0 1+(2703562767/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305270559/10000000000 : ℝ)*X 1 0+(-1882320373/10000000000 : ℝ)*X 1 1+(216285021/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652634971/5000000000 : ℝ)*X 2 0+(5407126231/10000000000 : ℝ)*X 2 1+(-941160123/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4301146853/10000000000 : ℝ)*X 0 0+(895529437/2000000000 : ℝ)*X 0 1+(4130945067/10000000000 : ℝ)*X 0 2+(4301146853/10000000000 : ℝ)*X 1 0+(895529437/2000000000 : ℝ)*X 1 1+(4130945067/10000000000 : ℝ)*X 1 2+(4301146853/10000000000 : ℝ)*X 2 0+(895529437/2000000000 : ℝ)*X 2 1+(4130945067/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (153588493125043649654187/17240000000000000000000000000 : ℝ) := by norm_num
    linear_combination (403639151/25000000000000 : ℝ)*(base19) + (376110371/25000000000000 : ℝ)*(base23) + (29439787/50000000000000 : ℝ)*(lower2) + (111001609/50000000000000 : ℝ)*(upper3) + (142025407/100000000000000 : ℝ)*(upper5) + (4543754805531889/100000000000000 : ℝ)*(major0) + (4543754805531889/100000000000000 : ℝ)*(major1) + (4543754805531889/100000000000000 : ℝ)*(major2) + (778005427983177/12500000000000 : ℝ)*(sp0) + (1244815175654799/20000000000000 : ℝ)*(sp1) + (3112037994194557/50000000000000 : ℝ)*(sp2) + (8948171430767/312500000000 : ℝ)*(sp3) + (17034482591/50000000000000 : ℝ)*(sp4) + (16963426219/100000000000000 : ℝ)*(sp7) + (1431715910635829/50000000000000 : ℝ)*(f.failure) + (3112038746415299/50000000000000 : ℝ)*(f.sum) + (49069113247151/17240000000000000000000000000 : ℝ)*base66 + (1629175748575302221/862000000000000000000000000000000 : ℝ)*base68 + (265804954632697779/862000000000000000000000000000000 : ℝ)*base69 + (1683245275253302221/862000000000000000000000000000000 : ℝ)*base72 + (140755810888769/17240000000000000000000000000 : ℝ)*base73 + (1238778353555302221/862000000000000000000000000000000 : ℝ)*base76 + (366009699680697779/862000000000000000000000000000000 : ℝ)*base77 + (1109948919436697779/862000000000000000000000000000000 : ℝ)*base79 + (55449785476671/17240000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (75513427/5000000000000000000000 : ℝ)*base90 + (75513427/5000000000000000000000 : ℝ)*base92 + (75513427/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (544578865562131868871259491/53875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (732058121/100000000000000 : ℝ)*(base19) + (216046639/50000000000000 : ℝ)*(base23) + (288791443/100000000000000 : ℝ)*(upper3) + (19373957/12500000000000 : ℝ)*(lower4) + (1144225948054273/25000000000000 : ℝ)*(major0) + (1144225948054273/25000000000000 : ℝ)*(major1) + (1144225948054273/25000000000000 : ℝ)*(major2) + (2610578957/100000000000000 : ℝ)*(sp1) + (9996264701/50000000000000 : ℝ)*(sp2) + (302427697/100000000000000 : ℝ)*(sp3) + (6269485244560293/100000000000000 : ℝ)*(sp4) + (1253896380384643/20000000000000 : ℝ)*(sp5) + (3134732409968807/50000000000000 : ℝ)*(sp6) + (72108042512661/2500000000000 : ℝ)*(sp7) + (1442161001467069/50000000000000 : ℝ)*(f.failure) + (6269485244560293/100000000000000 : ℝ)*(f.sum) + (30830223774043/4310000000000000000000000000 : ℝ)*base65 + (1000867233789676003/215500000000000000000000000000000 : ℝ)*base67 + (143632034256176003/215500000000000000000000000000000 : ℝ)*base69 + (3306511497879176003/215500000000000000000000000000000 : ℝ)*base71 + (2947981182773/4310000000000000000000000000 : ℝ)*base73 + (212504334591676003/215500000000000000000000000000000 : ℝ)*base75 + (347345907825176003/215500000000000000000000000000000 : ℝ)*base77 + (211889197631823997/215500000000000000000000000000000 : ℝ)*base80 + (10241898601143/4310000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (44046453/5000000000000000000000 : ℝ)*base89 + (44046453/5000000000000000000000 : ℝ)*base91 + (44046453/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1442_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158682137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1479/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5671/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11363/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1442_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1442_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158682137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15761/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2609/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11363/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1442_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1442_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1442_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158682137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15761/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2609/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11363/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1442_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

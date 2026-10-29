-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1743_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:13:43.474246+00:00
-- url     : https://prove2.me/submissions/bebe9229-545f-4e96-87cd-1e23985c2134

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
theorem support_rectangle_w1743_s0_0 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1211484029/10000000000 : ℝ)*x 0 + (1413149173/2500000000 : ℝ)*x 1 + (620855983/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1211484029/10000000000 : ℝ)^5663 ≤ (59396631001/781250000000 : ℝ)^4639 := by
    have hnat : (1211484029 : ℕ)^5663*781250000000^4639 ≤ 59396631001^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1211484029 10000000000 59396631001 781250000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1413149173/2500000000 : ℝ)^5663 ≤ (49837920198249/100000000000000 : ℝ)^4639 := by
    have hnat : (1413149173 : ℕ)^5663*100000000000000^4639 ≤ 49837920198249^4639*2500000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1413149173 2500000000 49837920198249 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (620855983/1250000000 : ℝ)^5663 ≤ (42559311017563/100000000000000 : ℝ)^4639 := by
    have hnat : (620855983 : ℕ)^5663*100000000000000^4639 ≤ 42559311017563^4639*1250000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      620855983 1250000000 42559311017563 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1211484029/10000000000 : ℝ), (1413149173/2500000000 : ℝ), (620855983/1250000000 : ℝ)] ![(59396631001/781250000000 : ℝ), (49837920198249/100000000000000 : ℝ), (42559311017563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1211484029/10000000000 : ℝ)|^5663 ≤ (59396631001/781250000000 : ℝ)^4639
        have hw : |(-1211484029/10000000000 : ℝ)|=(1211484029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1413149173/2500000000 : ℝ)|^5663 ≤ (49837920198249/100000000000000 : ℝ)^4639
        have hw : |(1413149173/2500000000 : ℝ)|=(1413149173/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(620855983/1250000000 : ℝ)|^5663 ≤ (42559311017563/100000000000000 : ℝ)^4639
        have hw : |(620855983/1250000000 : ℝ)|=(620855983/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_s0_1 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2690065919/5000000000 : ℝ)*x 0 + (-395167407/2500000000 : ℝ)*x 1 + (4966848089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2690065919/5000000000 : ℝ)^5663 ≤ (1876847059783/4000000000000 : ℝ)^4639 := by
    have hnat : (2690065919 : ℕ)^5663*4000000000000^4639 ≤ 1876847059783^4639*5000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690065919 5000000000 1876847059783 4000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (395167407/2500000000 : ℝ)^5663 ≤ (5259755060483/50000000000000 : ℝ)^4639 := by
    have hnat : (395167407 : ℕ)^5663*50000000000000^4639 ≤ 5259755060483^4639*2500000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      395167407 2500000000 5259755060483 50000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4966848089/10000000000 : ℝ)^5663 ≤ (21279656685543/50000000000000 : ℝ)^4639 := by
    have hnat : (4966848089 : ℕ)^5663*50000000000000^4639 ≤ 21279656685543^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4966848089 10000000000 21279656685543 50000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2690065919/5000000000 : ℝ), (-395167407/2500000000 : ℝ), (4966848089/10000000000 : ℝ)] ![(1876847059783/4000000000000 : ℝ), (5259755060483/50000000000000 : ℝ), (21279656685543/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2690065919/5000000000 : ℝ)|^5663 ≤ (1876847059783/4000000000000 : ℝ)^4639
        have hw : |(2690065919/5000000000 : ℝ)|=(2690065919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-395167407/2500000000 : ℝ)|^5663 ≤ (5259755060483/50000000000000 : ℝ)^4639
        have hw : |(-395167407/2500000000 : ℝ)|=(395167407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4966848089/10000000000 : ℝ)|^5663 ≤ (21279656685543/50000000000000 : ℝ)^4639
        have hw : |(4966848089/10000000000 : ℝ)|=(4966848089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_s0_2 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5380132573/10000000000 : ℝ)*x 0 + (4966847659/10000000000 : ℝ)*x 1 + (-790334609/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380132573/10000000000 : ℝ)^5663 ≤ (11730296079899/25000000000000 : ℝ)^4639 := by
    have hnat : (5380132573 : ℕ)^5663*25000000000000^4639 ≤ 11730296079899^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380132573 10000000000 11730296079899 25000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4966847659/10000000000 : ℝ)^5663 ≤ (21279654436621/50000000000000 : ℝ)^4639 := by
    have hnat : (4966847659 : ℕ)^5663*50000000000000^4639 ≤ 21279654436621^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4966847659 10000000000 21279654436621 50000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (790334609/5000000000 : ℝ)^5663 ≤ (420780271603/4000000000000 : ℝ)^4639 := by
    have hnat : (790334609 : ℕ)^5663*4000000000000^4639 ≤ 420780271603^4639*5000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      790334609 5000000000 420780271603 4000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380132573/10000000000 : ℝ), (4966847659/10000000000 : ℝ), (-790334609/5000000000 : ℝ)] ![(11730296079899/25000000000000 : ℝ), (21279654436621/50000000000000 : ℝ), (420780271603/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380132573/10000000000 : ℝ)|^5663 ≤ (11730296079899/25000000000000 : ℝ)^4639
        have hw : |(5380132573/10000000000 : ℝ)|=(5380132573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4966847659/10000000000 : ℝ)|^5663 ≤ (21279654436621/50000000000000 : ℝ)^4639
        have hw : |(4966847659/10000000000 : ℝ)|=(4966847659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-790334609/5000000000 : ℝ)|^5663 ≤ (420780271603/4000000000000 : ℝ)^4639
        have hw : |(-790334609/5000000000 : ℝ)|=(790334609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_s0_3 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1993994239/5000000000 : ℝ)*x 0 + (2977566359/10000000000 : ℝ)*x 1 + (206654971/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1993994239/5000000000 : ℝ)^5663 ≤ (6511115691301/20000000000000 : ℝ)^4639 := by
    have hnat : (1993994239 : ℕ)^5663*20000000000000^4639 ≤ 6511115691301^4639*5000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1993994239 5000000000 6511115691301 20000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2977566359/10000000000 : ℝ)^5663 ≤ (22788885371409/100000000000000 : ℝ)^4639 := by
    have hnat : (2977566359 : ℕ)^5663*100000000000000^4639 ≤ 22788885371409^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2977566359 10000000000 22788885371409 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (206654971/400000000 : ℝ)^5663 ≤ (11163884041051/25000000000000 : ℝ)^4639 := by
    have hnat : (206654971 : ℕ)^5663*25000000000000^4639 ≤ 11163884041051^4639*400000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206654971 400000000 11163884041051 25000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1993994239/5000000000 : ℝ), (2977566359/10000000000 : ℝ), (206654971/400000000 : ℝ)] ![(6511115691301/20000000000000 : ℝ), (22788885371409/100000000000000 : ℝ), (11163884041051/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1993994239/5000000000 : ℝ)|^5663 ≤ (6511115691301/20000000000000 : ℝ)^4639
        have hw : |(1993994239/5000000000 : ℝ)|=(1993994239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2977566359/10000000000 : ℝ)|^5663 ≤ (22788885371409/100000000000000 : ℝ)^4639
        have hw : |(2977566359/10000000000 : ℝ)|=(2977566359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(206654971/400000000 : ℝ)|^5663 ≤ (11163884041051/25000000000000 : ℝ)^4639
        have hw : |(206654971/400000000 : ℝ)|=(206654971/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_s0_4 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-606501669/5000000000 : ℝ)*x 0 + (4984514431/10000000000 : ℝ)*x 1 + (563433253/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (606501669/5000000000 : ℝ)^5663 ≤ (1903602389677/25000000000000 : ℝ)^4639 := by
    have hnat : (606501669 : ℕ)^5663*25000000000000^4639 ≤ 1903602389677^4639*5000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      606501669 5000000000 1903602389677 25000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4984514431/10000000000 : ℝ)^5663 ≤ (21372088794151/50000000000000 : ℝ)^4639 := by
    have hnat : (4984514431 : ℕ)^5663*50000000000000^4639 ≤ 21372088794151^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4984514431 10000000000 21372088794151 50000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (563433253/1000000000 : ℝ)^5663 ≤ (24820706420033/50000000000000 : ℝ)^4639 := by
    have hnat : (563433253 : ℕ)^5663*50000000000000^4639 ≤ 24820706420033^4639*1000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563433253 1000000000 24820706420033 50000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-606501669/5000000000 : ℝ), (4984514431/10000000000 : ℝ), (563433253/1000000000 : ℝ)] ![(1903602389677/25000000000000 : ℝ), (21372088794151/50000000000000 : ℝ), (24820706420033/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-606501669/5000000000 : ℝ)|^5663 ≤ (1903602389677/25000000000000 : ℝ)^4639
        have hw : |(-606501669/5000000000 : ℝ)|=(606501669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4984514431/10000000000 : ℝ)|^5663 ≤ (21372088794151/50000000000000 : ℝ)^4639
        have hw : |(4984514431/10000000000 : ℝ)|=(4984514431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(563433253/1000000000 : ℝ)|^5663 ≤ (24820706420033/50000000000000 : ℝ)^4639
        have hw : |(563433253/1000000000 : ℝ)|=(563433253/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_s0_5 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1039315703/2000000000 : ℝ)*x 0 + (-91318581/1000000000 : ℝ)*x 1 + (5634333781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1039315703/2000000000 : ℝ)^5663 ≤ (11243609911017/25000000000000 : ℝ)^4639 := by
    have hnat : (1039315703 : ℕ)^5663*25000000000000^4639 ≤ 11243609911017^4639*2000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039315703 2000000000 11243609911017 25000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (91318581/1000000000 : ℝ)^5663 ≤ (673016755487/12500000000000 : ℝ)^4639 := by
    have hnat : (91318581 : ℕ)^5663*12500000000000^4639 ≤ 673016755487^4639*1000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91318581 1000000000 673016755487 12500000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5634333781/10000000000 : ℝ)^5663 ≤ (49641426294987/100000000000000 : ℝ)^4639 := by
    have hnat : (5634333781 : ℕ)^5663*100000000000000^4639 ≤ 49641426294987^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5634333781 10000000000 49641426294987 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1039315703/2000000000 : ℝ), (-91318581/1000000000 : ℝ), (5634333781/10000000000 : ℝ)] ![(11243609911017/25000000000000 : ℝ), (673016755487/12500000000000 : ℝ), (49641426294987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1039315703/2000000000 : ℝ)|^5663 ≤ (11243609911017/25000000000000 : ℝ)^4639
        have hw : |(1039315703/2000000000 : ℝ)|=(1039315703/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-91318581/1000000000 : ℝ)|^5663 ≤ (673016755487/12500000000000 : ℝ)^4639
        have hw : |(-91318581/1000000000 : ℝ)|=(91318581/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5634333781/10000000000 : ℝ)|^5663 ≤ (49641426294987/100000000000000 : ℝ)^4639
        have hw : |(5634333781/10000000000 : ℝ)|=(5634333781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_s0_6 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (259829019/500000000 : ℝ)*x 0 + (1126866349/2000000000 : ℝ)*x 1 + (-182637223/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (259829019/500000000 : ℝ)^5663 ≤ (44974459347837/100000000000000 : ℝ)^4639 := by
    have hnat : (259829019 : ℕ)^5663*100000000000000^4639 ≤ 44974459347837^4639*500000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259829019 500000000 44974459347837 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1126866349/2000000000 : ℝ)^5663 ≤ (4964140439713/10000000000000 : ℝ)^4639 := by
    have hnat : (1126866349 : ℕ)^5663*10000000000000^4639 ≤ 4964140439713^4639*2000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126866349 2000000000 4964140439713 10000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (182637223/2000000000 : ℝ)^5663 ≤ (5384136239119/100000000000000 : ℝ)^4639 := by
    have hnat : (182637223 : ℕ)^5663*100000000000000^4639 ≤ 5384136239119^4639*2000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182637223 2000000000 5384136239119 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(259829019/500000000 : ℝ), (1126866349/2000000000 : ℝ), (-182637223/2000000000 : ℝ)] ![(44974459347837/100000000000000 : ℝ), (4964140439713/10000000000000 : ℝ), (5384136239119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(259829019/500000000 : ℝ)|^5663 ≤ (44974459347837/100000000000000 : ℝ)^4639
        have hw : |(259829019/500000000 : ℝ)|=(259829019/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1126866349/2000000000 : ℝ)|^5663 ≤ (4964140439713/10000000000000 : ℝ)^4639
        have hw : |(1126866349/2000000000 : ℝ)|=(1126866349/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-182637223/2000000000 : ℝ)|^5663 ≤ (5384136239119/100000000000000 : ℝ)^4639
        have hw : |(-182637223/2000000000 : ℝ)|=(182637223/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_s0_7 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3992845103/10000000000 : ℝ)*x 0 + (1021997089/2000000000 : ℝ)*x 1 + (1517932911/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3992845103/10000000000 : ℝ)^5663 ≤ (16301991528061/50000000000000 : ℝ)^4639 := by
    have hnat : (3992845103 : ℕ)^5663*50000000000000^4639 ≤ 16301991528061^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3992845103 10000000000 16301991528061 50000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1021997089/2000000000 : ℝ)^5663 ≤ (44061271722147/100000000000000 : ℝ)^4639 := by
    have hnat : (1021997089 : ℕ)^5663*100000000000000^4639 ≤ 44061271722147^4639*2000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021997089 2000000000 44061271722147 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1517932911/5000000000 : ℝ)^5663 ≤ (23334745208529/100000000000000 : ℝ)^4639 := by
    have hnat : (1517932911 : ℕ)^5663*100000000000000^4639 ≤ 23334745208529^4639*5000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1517932911 5000000000 23334745208529 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3992845103/10000000000 : ℝ), (1021997089/2000000000 : ℝ), (1517932911/5000000000 : ℝ)] ![(16301991528061/50000000000000 : ℝ), (44061271722147/100000000000000 : ℝ), (23334745208529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3992845103/10000000000 : ℝ)|^5663 ≤ (16301991528061/50000000000000 : ℝ)^4639
        have hw : |(3992845103/10000000000 : ℝ)|=(3992845103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1021997089/2000000000 : ℝ)|^5663 ≤ (44061271722147/100000000000000 : ℝ)^4639
        have hw : |(1021997089/2000000000 : ℝ)|=(1021997089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1517932911/5000000000 : ℝ)|^5663 ≤ (23334745208529/100000000000000 : ℝ)^4639
        have hw : |(1517932911/5000000000 : ℝ)|=(1517932911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1743_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (52398121/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (643/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (21227/100000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
  have base37 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
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
  have hpowlo : (0 : ℝ) ^ (5647/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5647 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5647*1^1024 ≤ 0^1024*1^5647 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5647 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5647 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5647/1024 : ℝ) ≤ (159749961303307369/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5647 ≤ (159749961303307369/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5647*25000000000000000000^1024 ≤ 159749961303307369^1024*5^5647 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 159749961303307369 25000000000000000000 5647 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (159749961303307369/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5647 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5647/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5647 := by
      have hnat : (1 : ℕ)^1024*1^5647 ≤ 1^5647*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5647 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5647 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25159749961303307369/25000000000000000000 : ℝ) ≤ (80092457012799/80000000000000 : ℝ) ^ (5647/1024 : ℝ) := by
    have hpowers : (25159749961303307369/25000000000000000000 : ℝ)^1024 ≤ (80092457012799/80000000000000 : ℝ)^5647 := by
      have hnat : (25159749961303307369 : ℕ)^1024*80000000000000^5647 ≤ 80092457012799^5647*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25159749961303307369 25000000000000000000 80092457012799 80000000000000 1024 5647 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80092457012799/80000000000000 : ℝ)) (X := (25159749961303307369/25000000000000000000 : ℝ)) (by norm_num) 5647 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12659749961303307369/12500000000000000000 : ℝ) ≤ (40092457012799/40000000000000 : ℝ) ^ (5647/1024 : ℝ) := by
    have hpowers : (12659749961303307369/12500000000000000000 : ℝ)^1024 ≤ (40092457012799/40000000000000 : ℝ)^5647 := by
      have hnat : (12659749961303307369 : ℕ)^1024*40000000000000^5647 ≤ 40092457012799^5647*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12659749961303307369 12500000000000000000 40092457012799 40000000000000 1024 5647 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (40092457012799/40000000000000 : ℝ)) (X := (12659749961303307369/12500000000000000000 : ℝ)) (by norm_num) 5647 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(92457012799/32000000000000 : ℝ)*(0 : ℝ))^(5647/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(92457012799/32000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(159749961303307369/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(92457012799/32000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5647/1024 : ℝ) := by
    rw [show (1 : ℝ)+(92457012799/32000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(80092457012799/80000000000000 : ℝ) by norm_num, show 1+(159749961303307369/25000000000000000000 : ℝ)+(0 : ℝ)=(25159749961303307369/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(159749961303307369/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(92457012799/32000000000000 : ℝ)*(2/5 : ℝ))^(5647/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(92457012799/32000000000000 : ℝ)*(2/5 : ℝ)=(40092457012799/40000000000000 : ℝ) by norm_num, show 1+2*(159749961303307369/25000000000000000000 : ℝ)=(12659749961303307369/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(92457012799/32000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5647/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (92457012799/32000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(92457012799/32000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5647/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (92457012799/32000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(92457012799/32000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5647/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (92457012799/32000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1211484029/10000000000 : ℝ)*X 0 0+(1413149173/2500000000 : ℝ)*X 0 1+(620855983/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2690065919/5000000000 : ℝ)*X 1 0+(-395167407/2500000000 : ℝ)*X 1 1+(4966848089/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5380132573/10000000000 : ℝ)*X 2 0+(4966847659/10000000000 : ℝ)*X 2 1+(-790334609/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1993994239/5000000000 : ℝ)*X 0 0+(2977566359/10000000000 : ℝ)*X 0 1+(206654971/400000000 : ℝ)*X 0 2+(1993994239/5000000000 : ℝ)*X 1 0+(2977566359/10000000000 : ℝ)*X 1 1+(206654971/400000000 : ℝ)*X 1 2+(1993994239/5000000000 : ℝ)*X 2 0+(2977566359/10000000000 : ℝ)*X 2 1+(206654971/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-606501669/5000000000 : ℝ)*X 0 0+(4984514431/10000000000 : ℝ)*X 0 1+(563433253/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1039315703/2000000000 : ℝ)*X 1 0+(-91318581/1000000000 : ℝ)*X 1 1+(5634333781/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((259829019/500000000 : ℝ)*X 2 0+(1126866349/2000000000 : ℝ)*X 2 1+(-182637223/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3992845103/10000000000 : ℝ)*X 0 0+(1021997089/2000000000 : ℝ)*X 0 1+(1517932911/5000000000 : ℝ)*X 0 2+(3992845103/10000000000 : ℝ)*X 1 0+(1021997089/2000000000 : ℝ)*X 1 1+(1517932911/5000000000 : ℝ)*X 1 2+(3992845103/10000000000 : ℝ)*X 2 0+(1021997089/2000000000 : ℝ)*X 2 1+(1517932911/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10687980809814507820851/1600000000000000000000000000 : ℝ) := by norm_num
    linear_combination (71755977/6250000000000 : ℝ)*(base19) + (332766619/25000000000000 : ℝ)*(base23) + (22793887/25000000000000 : ℝ)*(upper3) + (1748441/20000000000000 : ℝ)*(upper4) + (293832199/100000000000000 : ℝ)*(upper5) + (957573301206383/100000000000000 : ℝ)*(major0) + (957573301206383/100000000000000 : ℝ)*(major1) + (957573301206383/100000000000000 : ℝ)*(major2) + (1458264722979953/100000000000000 : ℝ)*(sp0) + (729135678839087/50000000000000 : ℝ)*(sp1) + (145827117470733/10000000000000 : ℝ)*(sp2) + (228435997197189/50000000000000 : ℝ)*(sp3) + (3891396927/50000000000000 : ℝ)*(sp4) + (1879578309/100000000000000 : ℝ)*(sp7) + (456873873972687/100000000000000 : ℝ)*(f.failure) + (1458272505773807/100000000000000 : ℝ)*(f.sum) + (2222223940817/1600000000000000000000000000 : ℝ)*base65 + (24638315726383/3200000000000000000000000000 : ℝ)*base68 + (6104418775983/3200000000000000000000000000 : ℝ)*base70 + (1701632737583/3200000000000000000000000000 : ℝ)*base72 + (3163137199983/1600000000000000000000000000 : ℝ)*base74 + (3944322107217/3200000000000000000000000000 : ℝ)*base75 + (2276852827183/3200000000000000000000000000 : ℝ)*base78 + (7196453070383/3200000000000000000000000000 : ℝ)*base80 + (3107950683217/1600000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (29121127/2500000000000000000000 : ℝ)*base89 + (29121127/2500000000000000000000 : ℝ)*base91 + (29121127/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1749858934932748551657/160000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11129717/100000000000000 : ℝ)*(base19) + (56028451/10000000000000 : ℝ)*(base23) + (12856381/2000000000000 : ℝ)*(base32) + (122967933/50000000000000 : ℝ)*(base37) + (24377209/25000000000000 : ℝ)*(upper3) + (202102385733181/20000000000000 : ℝ)*(major0) + (202102385733181/20000000000000 : ℝ)*(major1) + (202102385733181/20000000000000 : ℝ)*(major2) + (748071339/50000000000000 : ℝ)*(sp1) + (35182897/2500000000000 : ℝ)*(sp2) + (1538891734338517/100000000000000 : ℝ)*(sp4) + (769445113533061/50000000000000 : ℝ)*(sp5) + (1538889766738127/100000000000000 : ℝ)*(sp6) + (48213086968443/10000000000000 : ℝ)*(sp7) + (241065879219673/50000000000000 : ℝ)*(f.failure) + (1538891734338517/100000000000000 : ℝ)*(f.sum) + (466595489539/320000000000000000000000000 : ℝ)*base65 + (1261290529661/640000000000000000000000000 : ℝ)*base68 + (1298954077181/640000000000000000000000000 : ℝ)*base70 + (3424514278141/640000000000000000000000000 : ℝ)*base72 + (116537184899/320000000000000000000000000 : ℝ)*base73 + (297899110141/640000000000000000000000000 : ℝ)*base76 + (1303782441981/640000000000000000000000000 : ℝ)*base78 + (2466940262781/640000000000000000000000000 : ℝ)*base80 + (137752181181/320000000000000000000000000 : ℝ)*base82 + (1065567/1250000000000000000000 : ℝ)*base90 + (1065567/1250000000000000000000 : ℝ)*base92 + (1065567/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1743_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (52398121/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (643/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (21227/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1743_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1743_s1_0 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1260914021/10000000000 : ℝ)*x 0 + (688898703/1250000000 : ℝ)*x 1 + (1015064483/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1260914021/10000000000 : ℝ)^5663 ≤ (7983131415667/100000000000000 : ℝ)^4639 := by
    have hnat : (1260914021 : ℕ)^5663*100000000000000^4639 ≤ 7983131415667^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1260914021 10000000000 7983131415667 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (688898703/1250000000 : ℝ)^5663 ≤ (48320183052113/100000000000000 : ℝ)^4639 := by
    have hnat : (688898703 : ℕ)^5663*100000000000000^4639 ≤ 48320183052113^4639*1250000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688898703 1250000000 48320183052113 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1015064483/2000000000 : ℝ)^5663 ≤ (43696685514447/100000000000000 : ℝ)^4639 := by
    have hnat : (1015064483 : ℕ)^5663*100000000000000^4639 ≤ 43696685514447^4639*2000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015064483 2000000000 43696685514447 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1260914021/10000000000 : ℝ), (688898703/1250000000 : ℝ), (1015064483/2000000000 : ℝ)] ![(7983131415667/100000000000000 : ℝ), (48320183052113/100000000000000 : ℝ), (43696685514447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1260914021/10000000000 : ℝ)|^5663 ≤ (7983131415667/100000000000000 : ℝ)^4639
        have hw : |(-1260914021/10000000000 : ℝ)|=(1260914021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(688898703/1250000000 : ℝ)|^5663 ≤ (48320183052113/100000000000000 : ℝ)^4639
        have hw : |(688898703/1250000000 : ℝ)|=(688898703/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1015064483/2000000000 : ℝ)|^5663 ≤ (43696685514447/100000000000000 : ℝ)^4639
        have hw : |(1015064483/2000000000 : ℝ)|=(1015064483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_s1_1 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (333903813/625000000 : ℝ)*x 0 + (-1489407579/10000000000 : ℝ)*x 1 + (5075322303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (333903813/625000000 : ℝ)^5663 ≤ (23260216262833/50000000000000 : ℝ)^4639 := by
    have hnat : (333903813 : ℕ)^5663*50000000000000^4639 ≤ 23260216262833^4639*625000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      333903813 625000000 23260216262833 50000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1489407579/10000000000 : ℝ)^5663 ≤ (9782883125461/100000000000000 : ℝ)^4639 := by
    have hnat : (1489407579 : ℕ)^5663*100000000000000^4639 ≤ 9782883125461^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1489407579 10000000000 9782883125461 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5075322303/10000000000 : ℝ)^5663 ≤ (8739336867463/20000000000000 : ℝ)^4639 := by
    have hnat : (5075322303 : ℕ)^5663*20000000000000^4639 ≤ 8739336867463^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5075322303 10000000000 8739336867463 20000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(333903813/625000000 : ℝ), (-1489407579/10000000000 : ℝ), (5075322303/10000000000 : ℝ)] ![(23260216262833/50000000000000 : ℝ), (9782883125461/100000000000000 : ℝ), (8739336867463/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(333903813/625000000 : ℝ)|^5663 ≤ (23260216262833/50000000000000 : ℝ)^4639
        have hw : |(333903813/625000000 : ℝ)|=(333903813/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1489407579/10000000000 : ℝ)|^5663 ≤ (9782883125461/100000000000000 : ℝ)^4639
        have hw : |(-1489407579/10000000000 : ℝ)|=(1489407579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5075322303/10000000000 : ℝ)|^5663 ≤ (8739336867463/20000000000000 : ℝ)^4639
        have hw : |(5075322303/10000000000 : ℝ)|=(5075322303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_s1_2 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5342460579/10000000000 : ℝ)*x 0 + (5075322613/10000000000 : ℝ)*x 1 + (-1489407741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5342460579/10000000000 : ℝ)^5663 ≤ (2907526747843/6250000000000 : ℝ)^4639 := by
    have hnat : (5342460579 : ℕ)^5663*6250000000000^4639 ≤ 2907526747843^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5342460579 10000000000 2907526747843 6250000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5075322613/10000000000 : ℝ)^5663 ≤ (5462085949431/12500000000000 : ℝ)^4639 := by
    have hnat : (5075322613 : ℕ)^5663*12500000000000^4639 ≤ 5462085949431^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5075322613 10000000000 5462085949431 12500000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1489407741/10000000000 : ℝ)^5663 ≤ (1956576884881/20000000000000 : ℝ)^4639 := by
    have hnat : (1489407741 : ℕ)^5663*20000000000000^4639 ≤ 1956576884881^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1489407741 10000000000 1956576884881 20000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5342460579/10000000000 : ℝ), (5075322613/10000000000 : ℝ), (-1489407741/10000000000 : ℝ)] ![(2907526747843/6250000000000 : ℝ), (5462085949431/12500000000000 : ℝ), (1956576884881/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5342460579/10000000000 : ℝ)|^5663 ≤ (2907526747843/6250000000000 : ℝ)^4639
        have hw : |(5342460579/10000000000 : ℝ)|=(5342460579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5075322613/10000000000 : ℝ)|^5663 ≤ (5462085949431/12500000000000 : ℝ)^4639
        have hw : |(5075322613/10000000000 : ℝ)|=(5075322613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1489407741/10000000000 : ℝ)|^5663 ≤ (1956576884881/20000000000000 : ℝ)^4639
        have hw : |(-1489407741/10000000000 : ℝ)|=(1489407741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_s1_3 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (806921023/2000000000 : ℝ)*x 0 + (1686350269/5000000000 : ℝ)*x 1 + (4763921969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (806921023/2000000000 : ℝ)^5663 ≤ (4127591039499/12500000000000 : ℝ)^4639 := by
    have hnat : (806921023 : ℕ)^5663*12500000000000^4639 ≤ 4127591039499^4639*2000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806921023 2000000000 4127591039499 12500000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1686350269/5000000000 : ℝ)^5663 ≤ (13266455675259/50000000000000 : ℝ)^4639 := by
    have hnat : (1686350269 : ℕ)^5663*50000000000000^4639 ≤ 13266455675259^4639*5000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1686350269 5000000000 13266455675259 50000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4763921969/10000000000 : ℝ)^5663 ≤ (10111590080757/25000000000000 : ℝ)^4639 := by
    have hnat : (4763921969 : ℕ)^5663*25000000000000^4639 ≤ 10111590080757^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4763921969 10000000000 10111590080757 25000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(806921023/2000000000 : ℝ), (1686350269/5000000000 : ℝ), (4763921969/10000000000 : ℝ)] ![(4127591039499/12500000000000 : ℝ), (13266455675259/50000000000000 : ℝ), (10111590080757/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(806921023/2000000000 : ℝ)|^5663 ≤ (4127591039499/12500000000000 : ℝ)^4639
        have hw : |(806921023/2000000000 : ℝ)|=(806921023/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1686350269/5000000000 : ℝ)|^5663 ≤ (13266455675259/50000000000000 : ℝ)^4639
        have hw : |(1686350269/5000000000 : ℝ)|=(1686350269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4763921969/10000000000 : ℝ)|^5663 ≤ (10111590080757/25000000000000 : ℝ)^4639
        have hw : |(4763921969/10000000000 : ℝ)|=(4763921969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_s1_4 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-315325327/2500000000 : ℝ)*x 0 + (2541232041/5000000000 : ℝ)*x 1 + (5503894837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (315325327/2500000000 : ℝ)^5663 ≤ (798612476659/10000000000000 : ℝ)^4639 := by
    have hnat : (315325327 : ℕ)^5663*10000000000000^4639 ≤ 798612476659^4639*2500000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315325327 2500000000 798612476659 10000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2541232041/5000000000 : ℝ)^5663 ≤ (43771756836217/100000000000000 : ℝ)^4639 := by
    have hnat : (2541232041 : ℕ)^5663*100000000000000^4639 ≤ 43771756836217^4639*5000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2541232041 5000000000 43771756836217 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5503894837/10000000000 : ℝ)^5663 ≤ (48242118378203/100000000000000 : ℝ)^4639 := by
    have hnat : (5503894837 : ℕ)^5663*100000000000000^4639 ≤ 48242118378203^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5503894837 10000000000 48242118378203 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-315325327/2500000000 : ℝ), (2541232041/5000000000 : ℝ), (5503894837/10000000000 : ℝ)] ![(798612476659/10000000000000 : ℝ), (43771756836217/100000000000000 : ℝ), (48242118378203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-315325327/2500000000 : ℝ)|^5663 ≤ (798612476659/10000000000000 : ℝ)^4639
        have hw : |(-315325327/2500000000 : ℝ)|=(315325327/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2541232041/5000000000 : ℝ)|^5663 ≤ (43771756836217/100000000000000 : ℝ)^4639
        have hw : |(2541232041/5000000000 : ℝ)|=(2541232041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5503894837/10000000000 : ℝ)|^5663 ≤ (48242118378203/100000000000000 : ℝ)^4639
        have hw : |(5503894837/10000000000 : ℝ)|=(5503894837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_s1_5 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2613347623/5000000000 : ℝ)*x 0 + (-265208707/2500000000 : ℝ)*x 1 + (1100779037/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2613347623/5000000000 : ℝ)^5663 ≤ (45292826824709/100000000000000 : ℝ)^4639 := by
    have hnat : (2613347623 : ℕ)^5663*100000000000000^4639 ≤ 45292826824709^4639*5000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613347623 5000000000 45292826824709 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (265208707/2500000000 : ℝ)^5663 ≤ (3232525529817/50000000000000 : ℝ)^4639 := by
    have hnat : (265208707 : ℕ)^5663*50000000000000^4639 ≤ 3232525529817^4639*2500000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265208707 2500000000 3232525529817 50000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1100779037/2000000000 : ℝ)^5663 ≤ (48242122101757/100000000000000 : ℝ)^4639 := by
    have hnat : (1100779037 : ℕ)^5663*100000000000000^4639 ≤ 48242122101757^4639*2000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100779037 2000000000 48242122101757 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2613347623/5000000000 : ℝ), (-265208707/2500000000 : ℝ), (1100779037/2000000000 : ℝ)] ![(45292826824709/100000000000000 : ℝ), (3232525529817/50000000000000 : ℝ), (48242122101757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2613347623/5000000000 : ℝ)|^5663 ≤ (45292826824709/100000000000000 : ℝ)^4639
        have hw : |(2613347623/5000000000 : ℝ)|=(2613347623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-265208707/2500000000 : ℝ)|^5663 ≤ (3232525529817/50000000000000 : ℝ)^4639
        have hw : |(-265208707/2500000000 : ℝ)|=(265208707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1100779037/2000000000 : ℝ)|^5663 ≤ (48242122101757/100000000000000 : ℝ)^4639
        have hw : |(1100779037/2000000000 : ℝ)|=(1100779037/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_s1_6 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2613347517/5000000000 : ℝ)*x 0 + (2751947649/5000000000 : ℝ)*x 1 + (-1060834967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2613347517/5000000000 : ℝ)^5663 ≤ (9058564916413/20000000000000 : ℝ)^4639 := by
    have hnat : (2613347517 : ℕ)^5663*20000000000000^4639 ≤ 9058564916413^4639*5000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613347517 5000000000 9058564916413 20000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2751947649/5000000000 : ℝ)^5663 ≤ (24121061655421/50000000000000 : ℝ)^4639 := by
    have hnat : (2751947649 : ℕ)^5663*50000000000000^4639 ≤ 24121061655421^4639*5000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2751947649 5000000000 24121061655421 50000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1060834967/10000000000 : ℝ)^5663 ≤ (6465052093731/100000000000000 : ℝ)^4639 := by
    have hnat : (1060834967 : ℕ)^5663*100000000000000^4639 ≤ 6465052093731^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060834967 10000000000 6465052093731 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2613347517/5000000000 : ℝ), (2751947649/5000000000 : ℝ), (-1060834967/10000000000 : ℝ)] ![(9058564916413/20000000000000 : ℝ), (24121061655421/50000000000000 : ℝ), (6465052093731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2613347517/5000000000 : ℝ)|^5663 ≤ (9058564916413/20000000000000 : ℝ)^4639
        have hw : |(2613347517/5000000000 : ℝ)|=(2613347517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2751947649/5000000000 : ℝ)|^5663 ≤ (24121061655421/50000000000000 : ℝ)^4639
        have hw : |(2751947649/5000000000 : ℝ)|=(2751947649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1060834967/10000000000 : ℝ)|^5663 ≤ (6465052093731/100000000000000 : ℝ)^4639
        have hw : |(-1060834967/10000000000 : ℝ)|=(1060834967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_s1_7 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4035841613/10000000000 : ℝ)*x 0 + (47411283/100000000 : ℝ)*x 1 + (1697991323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4035841613/10000000000 : ℝ)^5663 ≤ (16516541276221/50000000000000 : ℝ)^4639 := by
    have hnat : (4035841613 : ℕ)^5663*50000000000000^4639 ≤ 16516541276221^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4035841613 10000000000 16516541276221 50000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (47411283/100000000 : ℝ)^5663 ≤ (10052561606741/25000000000000 : ℝ)^4639 := by
    have hnat : (47411283 : ℕ)^5663*25000000000000^4639 ≤ 10052561606741^4639*100000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47411283 100000000 10052561606741 25000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1697991323/5000000000 : ℝ)^5663 ≤ (26756671002879/100000000000000 : ℝ)^4639 := by
    have hnat : (1697991323 : ℕ)^5663*100000000000000^4639 ≤ 26756671002879^4639*5000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1697991323 5000000000 26756671002879 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4035841613/10000000000 : ℝ), (47411283/100000000 : ℝ), (1697991323/5000000000 : ℝ)] ![(16516541276221/50000000000000 : ℝ), (10052561606741/25000000000000 : ℝ), (26756671002879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4035841613/10000000000 : ℝ)|^5663 ≤ (16516541276221/50000000000000 : ℝ)^4639
        have hw : |(4035841613/10000000000 : ℝ)|=(4035841613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(47411283/100000000 : ℝ)|^5663 ≤ (10052561606741/25000000000000 : ℝ)^4639
        have hw : |(47411283/100000000 : ℝ)|=(47411283/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1697991323/5000000000 : ℝ)|^5663 ≤ (26756671002879/100000000000000 : ℝ)^4639
        have hw : |(1697991323/5000000000 : ℝ)|=(1697991323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1743_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (52398121/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21227/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (643/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (1773/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18209/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (21227/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (643/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (21227/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (643/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (21227/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (643/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (21227/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (643/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (21227/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (643/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (21227/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (643/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (643/10000 : ℝ) ^ (5647/1024 : ℝ) ≤ (13386668482987/50000000000000000000 : ℝ) := by
    have hpowers : (643/10000 : ℝ)^5647 ≤ (13386668482987/50000000000000000000 : ℝ)^1024 := by
      have hnat : (643 : ℕ)^5647*50000000000000000000^1024 ≤ 13386668482987^1024*10000^5647 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        643 10000 13386668482987 50000000000000000000 5647 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (643/10000 : ℝ)) (X := (13386668482987/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5647 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (21227/100000 : ℝ) ^ (5647/1024 : ℝ) ≤ (3882016483957587/20000000000000000000 : ℝ) := by
    have hpowers : (21227/100000 : ℝ)^5647 ≤ (3882016483957587/20000000000000000000 : ℝ)^1024 := by
      have hnat : (21227 : ℕ)^5647*20000000000000000000^1024 ≤ 3882016483957587^1024*100000^5647 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21227 100000 3882016483957587 20000000000000000000 5647 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21227/100000 : ℝ)) (X := (3882016483957587/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5647 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000013386668482987/25000000000000000000 : ℝ) ≤ (10000000970989589/10000000000000000 : ℝ) ^ (5647/1024 : ℝ) := by
    have hpowers : (25000013386668482987/25000000000000000000 : ℝ)^1024 ≤ (10000000970989589/10000000000000000 : ℝ)^5647 := by
      have hnat : (25000013386668482987 : ℕ)^1024*10000000000000000^5647 ≤ 10000000970989589^5647*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000013386668482987 25000000000000000000 10000000970989589 10000000000000000 1024 5647 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000970989589/10000000000000000 : ℝ)) (X := (25000013386668482987/25000000000000000000 : ℝ)) (by norm_num) 5647 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100019436855756753909/100000000000000000000 : ℝ) ≤ (10000352430617053/10000000000000000 : ℝ) ^ (5647/1024 : ℝ) := by
    have hpowers : (100019436855756753909/100000000000000000000 : ℝ)^1024 ≤ (10000352430617053/10000000000000000 : ℝ)^5647 := by
      have hnat : (100019436855756753909 : ℕ)^1024*10000000000000000^5647 ≤ 10000352430617053^5647*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100019436855756753909 100000000000000000000 10000352430617053 10000000000000000 1024 5647 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000352430617053/10000000000000000 : ℝ)) (X := (100019436855756753909/100000000000000000000 : ℝ)) (by norm_num) 5647 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10003882016483957587/10000000000000000000 : ℝ) ≤ (10000703890244517/10000000000000000 : ℝ) ^ (5647/1024 : ℝ) := by
    have hpowers : (10003882016483957587/10000000000000000000 : ℝ)^1024 ≤ (10000703890244517/10000000000000000 : ℝ)^5647 := by
      have hnat : (10003882016483957587 : ℕ)^1024*10000000000000000^5647 ≤ 10000703890244517^5647*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003882016483957587 10000000000000000000 10000703890244517 10000000000000000 1024 5647 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000703890244517/10000000000000000 : ℝ)) (X := (10003882016483957587/10000000000000000000 : ℝ)) (by norm_num) 5647 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13386668482987/50000000000000000000 : ℝ) ≤ ((147965494596923761393/147970000000000000000 : ℝ)+2*(43932453433/184962500000000 : ℝ)*(643/10000 : ℝ))^(5647/1024 : ℝ) := by
    rw [show (147965494596923761393/147970000000000000000 : ℝ)+2*(43932453433/184962500000000 : ℝ)*(643/10000 : ℝ)=(10000000970989589/10000000000000000 : ℝ) by norm_num, show 1+2*(13386668482987/50000000000000000000 : ℝ)=(25000013386668482987/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3882016483957587/20000000000000000000 : ℝ)+(13386668482987/50000000000000000000 : ℝ) ≤ ((147965494596923761393/147970000000000000000 : ℝ)+(43932453433/184962500000000 : ℝ)*((21227/100000 : ℝ)+(643/10000 : ℝ)))^(5647/1024 : ℝ) := by
    rw [show (147965494596923761393/147970000000000000000 : ℝ)+(43932453433/184962500000000 : ℝ)*((21227/100000 : ℝ)+(643/10000 : ℝ))=(10000352430617053/10000000000000000 : ℝ) by norm_num, show 1+(3882016483957587/20000000000000000000 : ℝ)+(13386668482987/50000000000000000000 : ℝ)=(100019436855756753909/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3882016483957587/20000000000000000000 : ℝ) ≤ ((147965494596923761393/147970000000000000000 : ℝ)+2*(43932453433/184962500000000 : ℝ)*(21227/100000 : ℝ))^(5647/1024 : ℝ) := by
    rw [show (147965494596923761393/147970000000000000000 : ℝ)+2*(43932453433/184962500000000 : ℝ)*(21227/100000 : ℝ)=(10000703890244517/10000000000000000 : ℝ) by norm_num, show 1+2*(3882016483957587/20000000000000000000 : ℝ)=(10003882016483957587/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (147965494596923761393/147970000000000000000 : ℝ)*(X 1 0+X 2 0)+(43932453433/184962500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5647/1024 : ℝ)) (lo := (643/10000 : ℝ)) (hi := (21227/100000 : ℝ)) (c := (147965494596923761393/147970000000000000000 : ℝ)) (alpha := (43932453433/184962500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (147965494596923761393/147970000000000000000 : ℝ)*(X 0 1+X 2 1)+(43932453433/184962500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5647/1024 : ℝ)) (lo := (643/10000 : ℝ)) (hi := (21227/100000 : ℝ)) (c := (147965494596923761393/147970000000000000000 : ℝ)) (alpha := (43932453433/184962500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (147965494596923761393/147970000000000000000 : ℝ)*(X 0 2+X 1 2)+(43932453433/184962500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5647/1024 : ℝ)) (lo := (643/10000 : ℝ)) (hi := (21227/100000 : ℝ)) (c := (147965494596923761393/147970000000000000000 : ℝ)) (alpha := (43932453433/184962500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1260914021/10000000000 : ℝ)*X 0 0+(688898703/1250000000 : ℝ)*X 0 1+(1015064483/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((333903813/625000000 : ℝ)*X 1 0+(-1489407579/10000000000 : ℝ)*X 1 1+(5075322303/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5342460579/10000000000 : ℝ)*X 2 0+(5075322613/10000000000 : ℝ)*X 2 1+(-1489407741/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((806921023/2000000000 : ℝ)*X 0 0+(1686350269/5000000000 : ℝ)*X 0 1+(4763921969/10000000000 : ℝ)*X 0 2+(806921023/2000000000 : ℝ)*X 1 0+(1686350269/5000000000 : ℝ)*X 1 1+(4763921969/10000000000 : ℝ)*X 1 2+(806921023/2000000000 : ℝ)*X 2 0+(1686350269/5000000000 : ℝ)*X 2 1+(4763921969/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-315325327/2500000000 : ℝ)*X 0 0+(2541232041/5000000000 : ℝ)*X 0 1+(5503894837/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2613347623/5000000000 : ℝ)*X 1 0+(-265208707/2500000000 : ℝ)*X 1 1+(1100779037/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2613347517/5000000000 : ℝ)*X 2 0+(2751947649/5000000000 : ℝ)*X 2 1+(-1060834967/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4035841613/10000000000 : ℝ)*X 0 0+(47411283/100000000 : ℝ)*X 0 1+(1697991323/5000000000 : ℝ)*X 0 2+(4035841613/10000000000 : ℝ)*X 1 0+(47411283/100000000 : ℝ)*X 1 1+(1697991323/5000000000 : ℝ)*X 1 2+(4035841613/10000000000 : ℝ)*X 2 0+(47411283/100000000 : ℝ)*X 2 1+(1697991323/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (254412021269868846281388447/18496250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (104067083/5000000000000 : ℝ)*(base19) + (855140167/50000000000000 : ℝ)*(base23) + (19962471/20000000000000 : ℝ)*(lower2) + (402457919/100000000000000 : ℝ)*(upper3) + (30314939/20000000000000 : ℝ)*(upper5) + (3766387175431/250000000000 : ℝ)*(major0) + (3766387175431/250000000000 : ℝ)*(major1) + (3766387175431/250000000000 : ℝ)*(major2) + (1147146700875509/50000000000000 : ℝ)*(sp0) + (1147152623316323/50000000000000 : ℝ)*(sp1) + (1147152808846987/50000000000000 : ℝ)*(sp2) + (28751869595769/4000000000000 : ℝ)*(sp3) + (1392622329/10000000000000 : ℝ)*(sp4) + (2606991641/50000000000000 : ℝ)*(sp7) + (718801953877507/100000000000000 : ℝ)*(f.failure) + (2294307327974307/100000000000000 : ℝ)*(f.sum) + (41851607313551/14797000000000000000000000000 : ℝ)*base66 + (274694056714699617/36992500000000000000000000000000 : ℝ)*base68 + (477290686699187117/36992500000000000000000000000000 : ℝ)*base70 + (7218351894347117/36992500000000000000000000000000 : ℝ)*base72 + (354430875577/924812500000000000000000000 : ℝ)*base74 + (5528350493652117/36992500000000000000000000000000 : ℝ)*base76 + (614856556802012117/36992500000000000000000000000000 : ℝ)*base78 + (496135861611824617/36992500000000000000000000000000 : ℝ)*base80 + (41461150292291/14797000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (30964347/2500000000000000000000 : ℝ)*base89 + (30964347/2500000000000000000000 : ℝ)*base91 + (30964347/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (104627161296301151638468462077/7398500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (938799363/50000000000000 : ℝ)*(base19) + (1039124647/50000000000000 : ℝ)*(base23) + (182405643/50000000000000 : ℝ)*(upper3) + (2555459/2000000000000 : ℝ)*(lower4) + (115248961/50000000000000 : ℝ)*(upper5) + (1558140025362737/100000000000000 : ℝ)*(major0) + (1558140025362737/100000000000000 : ℝ)*(major1) + (1558140025362737/100000000000000 : ℝ)*(major2) + (13112180559/100000000000000 : ℝ)*(sp1) + (15479549553/100000000000000 : ℝ)*(sp2) + (1186432752367487/50000000000000 : ℝ)*(sp4) + (296606314369461/12500000000000 : ℝ)*(sp5) + (1186423973468063/50000000000000 : ℝ)*(sp6) + (46463379662589/6250000000000 : ℝ)*(sp7) + (46463379662589/6250000000000 : ℝ)*(f.failure) + (1186432752367487/50000000000000 : ℝ)*(f.sum) + (906717343637/1156015625000000000000000000 : ℝ)*base65 + (33357353167037787359/14797000000000000000000000000000000 : ℝ)*base68 + (85216607320015787359/14797000000000000000000000000000000 : ℝ)*base70 + (55232928555454212641/14797000000000000000000000000000000 : ℝ)*base71 + (58853809227907/73985000000000000000000000000 : ℝ)*base74 + (43882180500041212641/14797000000000000000000000000000000 : ℝ)*base75 + (52635067340907212641/14797000000000000000000000000000000 : ℝ)*base77 + (18306761952769212641/14797000000000000000000000000000000 : ℝ)*base79 + (28837695227303/73985000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1032769/156250000000000000000 : ℝ)*base89 + (1032769/156250000000000000000 : ℝ)*base91 + (1032769/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1743_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (52398121/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21227/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (643/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1773/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18209/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1743_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1743_s2_0 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-631153027/5000000000 : ℝ)*x 0 + (5506737133/10000000000 : ℝ)*x 1 + (2539416087/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (631153027/5000000000 : ℝ)^5663 ≤ (3996945709713/50000000000000 : ℝ)^4639 := by
    have hnat : (631153027 : ℕ)^5663*50000000000000^4639 ≤ 3996945709713^4639*5000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      631153027 5000000000 3996945709713 50000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5506737133/10000000000 : ℝ)^5663 ≤ (9654506460839/20000000000000 : ℝ)^4639 := by
    have hnat : (5506737133 : ℕ)^5663*20000000000000^4639 ≤ 9654506460839^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5506737133 10000000000 9654506460839 20000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2539416087/5000000000 : ℝ)^5663 ≤ (43733576264461/100000000000000 : ℝ)^4639 := by
    have hnat : (2539416087 : ℕ)^5663*100000000000000^4639 ≤ 43733576264461^4639*5000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2539416087 5000000000 43733576264461 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-631153027/5000000000 : ℝ), (5506737133/10000000000 : ℝ), (2539416087/5000000000 : ℝ)] ![(3996945709713/50000000000000 : ℝ), (9654506460839/20000000000000 : ℝ), (43733576264461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-631153027/5000000000 : ℝ)|^5663 ≤ (3996945709713/50000000000000 : ℝ)^4639
        have hw : |(-631153027/5000000000 : ℝ)|=(631153027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5506737133/10000000000 : ℝ)|^5663 ≤ (9654506460839/20000000000000 : ℝ)^4639
        have hw : |(5506737133/10000000000 : ℝ)|=(5506737133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2539416087/5000000000 : ℝ)|^5663 ≤ (43733576264461/100000000000000 : ℝ)^4639
        have hw : |(2539416087/5000000000 : ℝ)|=(2539416087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_s2_1 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5341232859/10000000000 : ℝ)*x 0 + (-1486434737/10000000000 : ℝ)*x 1 + (634853953/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5341232859/10000000000 : ℝ)^5663 ≤ (46507377894351/100000000000000 : ℝ)^4639 := by
    have hnat : (5341232859 : ℕ)^5663*100000000000000^4639 ≤ 46507377894351^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5341232859 10000000000 46507377894351 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1486434737/10000000000 : ℝ)^5663 ≤ (1951810322773/20000000000000 : ℝ)^4639 := by
    have hnat : (1486434737 : ℕ)^5663*20000000000000^4639 ≤ 1951810322773^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1486434737 10000000000 1951810322773 20000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (634853953/1250000000 : ℝ)^5663 ≤ (43733570483021/100000000000000 : ℝ)^4639 := by
    have hnat : (634853953 : ℕ)^5663*100000000000000^4639 ≤ 43733570483021^4639*1250000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      634853953 1250000000 43733570483021 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5341232859/10000000000 : ℝ), (-1486434737/10000000000 : ℝ), (634853953/1250000000 : ℝ)] ![(46507377894351/100000000000000 : ℝ), (1951810322773/20000000000000 : ℝ), (43733570483021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5341232859/10000000000 : ℝ)|^5663 ≤ (46507377894351/100000000000000 : ℝ)^4639
        have hw : |(5341232859/10000000000 : ℝ)|=(5341232859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1486434737/10000000000 : ℝ)|^5663 ≤ (1951810322773/20000000000000 : ℝ)^4639
        have hw : |(-1486434737/10000000000 : ℝ)|=(1486434737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(634853953/1250000000 : ℝ)|^5663 ≤ (43733570483021/100000000000000 : ℝ)^4639
        have hw : |(634853953/1250000000 : ℝ)|=(634853953/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_s2_2 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5341232033/10000000000 : ℝ)*x 0 + (2539416037/5000000000 : ℝ)*x 1 + (-743217621/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5341232033/10000000000 : ℝ)^5663 ≤ (46507369114593/100000000000000 : ℝ)^4639 := by
    have hnat : (5341232033 : ℕ)^5663*100000000000000^4639 ≤ 46507369114593^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5341232033 10000000000 46507369114593 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2539416037/5000000000 : ℝ)^5663 ≤ (4373357521329/10000000000000 : ℝ)^4639 := by
    have hnat : (2539416037 : ℕ)^5663*10000000000000^4639 ≤ 4373357521329^4639*5000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2539416037 5000000000 4373357521329 10000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (743217621/5000000000 : ℝ)^5663 ≤ (4879527830629/50000000000000 : ℝ)^4639 := by
    have hnat : (743217621 : ℕ)^5663*50000000000000^4639 ≤ 4879527830629^4639*5000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      743217621 5000000000 4879527830629 50000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5341232033/10000000000 : ℝ), (2539416037/5000000000 : ℝ), (-743217621/5000000000 : ℝ)] ![(46507369114593/100000000000000 : ℝ), (4373357521329/10000000000000 : ℝ), (4879527830629/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5341232033/10000000000 : ℝ)|^5663 ≤ (46507369114593/100000000000000 : ℝ)^4639
        have hw : |(5341232033/10000000000 : ℝ)|=(5341232033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2539416037/5000000000 : ℝ)|^5663 ≤ (4373357521329/10000000000000 : ℝ)^4639
        have hw : |(2539416037/5000000000 : ℝ)|=(2539416037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-743217621/5000000000 : ℝ)|^5663 ≤ (4879527830629/50000000000000 : ℝ)^4639
        have hw : |(-743217621/5000000000 : ℝ)|=(743217621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_s2_3 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (807148131/2000000000 : ℝ)*x 0 + (1692659299/5000000000 : ℝ)*x 1 + (593890847/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (807148131/2000000000 : ℝ)^5663 ≤ (33032073818307/100000000000000 : ℝ)^4639 := by
    have hnat : (807148131 : ℕ)^5663*100000000000000^4639 ≤ 33032073818307^4639*2000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      807148131 2000000000 33032073818307 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1692659299/5000000000 : ℝ)^5663 ≤ (2665413881367/10000000000000 : ℝ)^4639 := by
    have hnat : (1692659299 : ℕ)^5663*10000000000000^4639 ≤ 2665413881367^4639*5000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1692659299 5000000000 2665413881367 10000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (593890847/1250000000 : ℝ)^5663 ≤ (20156893676057/50000000000000 : ℝ)^4639 := by
    have hnat : (593890847 : ℕ)^5663*50000000000000^4639 ≤ 20156893676057^4639*1250000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      593890847 1250000000 20156893676057 50000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(807148131/2000000000 : ℝ), (1692659299/5000000000 : ℝ), (593890847/1250000000 : ℝ)] ![(33032073818307/100000000000000 : ℝ), (2665413881367/10000000000000 : ℝ), (20156893676057/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(807148131/2000000000 : ℝ)|^5663 ≤ (33032073818307/100000000000000 : ℝ)^4639
        have hw : |(807148131/2000000000 : ℝ)|=(807148131/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1692659299/5000000000 : ℝ)|^5663 ≤ (2665413881367/10000000000000 : ℝ)^4639
        have hw : |(1692659299/5000000000 : ℝ)|=(1692659299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(593890847/1250000000 : ℝ)|^5663 ≤ (20156893676057/50000000000000 : ℝ)^4639
        have hw : |(593890847/1250000000 : ℝ)|=(593890847/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_s2_4 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1262672443/10000000000 : ℝ)*x 0 + (2542857503/5000000000 : ℝ)*x 1 + (1374927353/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1262672443/10000000000 : ℝ)^5663 ≤ (3998361966849/50000000000000 : ℝ)^4639 := by
    have hnat : (1262672443 : ℕ)^5663*50000000000000^4639 ≤ 3998361966849^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1262672443 10000000000 3998361966849 50000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2542857503/5000000000 : ℝ)^5663 ≤ (10951484351907/25000000000000 : ℝ)^4639 := by
    have hnat : (2542857503 : ℕ)^5663*25000000000000^4639 ≤ 10951484351907^4639*5000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2542857503 5000000000 10951484351907 25000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1374927353/2500000000 : ℝ)^5663 ≤ (9639467728271/20000000000000 : ℝ)^4639 := by
    have hnat : (1374927353 : ℕ)^5663*20000000000000^4639 ≤ 9639467728271^4639*2500000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1374927353 2500000000 9639467728271 20000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1262672443/10000000000 : ℝ), (2542857503/5000000000 : ℝ), (1374927353/2500000000 : ℝ)] ![(3998361966849/50000000000000 : ℝ), (10951484351907/25000000000000 : ℝ), (9639467728271/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1262672443/10000000000 : ℝ)|^5663 ≤ (3998361966849/50000000000000 : ℝ)^4639
        have hw : |(-1262672443/10000000000 : ℝ)|=(1262672443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2542857503/5000000000 : ℝ)|^5663 ≤ (10951484351907/25000000000000 : ℝ)^4639
        have hw : |(2542857503/5000000000 : ℝ)|=(2542857503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1374927353/2500000000 : ℝ)|^5663 ≤ (9639467728271/20000000000000 : ℝ)^4639
        have hw : |(1374927353/2500000000 : ℝ)|=(1374927353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_s2_5 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1306901383/2500000000 : ℝ)*x 0 + (-532778907/5000000000 : ℝ)*x 1 + (5499709383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1306901383/2500000000 : ℝ)^5663 ≤ (22651228238973/50000000000000 : ℝ)^4639 := by
    have hnat : (1306901383 : ℕ)^5663*50000000000000^4639 ≤ 22651228238973^4639*2500000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306901383 2500000000 22651228238973 50000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (532778907/5000000000 : ℝ)^5663 ≤ (3250102586163/50000000000000 : ℝ)^4639 := by
    have hnat : (532778907 : ℕ)^5663*50000000000000^4639 ≤ 3250102586163^4639*5000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532778907 5000000000 3250102586163 50000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5499709383/10000000000 : ℝ)^5663 ≤ (48197338331111/100000000000000 : ℝ)^4639 := by
    have hnat : (5499709383 : ℕ)^5663*100000000000000^4639 ≤ 48197338331111^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5499709383 10000000000 48197338331111 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1306901383/2500000000 : ℝ), (-532778907/5000000000 : ℝ), (5499709383/10000000000 : ℝ)] ![(22651228238973/50000000000000 : ℝ), (3250102586163/50000000000000 : ℝ), (48197338331111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1306901383/2500000000 : ℝ)|^5663 ≤ (22651228238973/50000000000000 : ℝ)^4639
        have hw : |(1306901383/2500000000 : ℝ)|=(1306901383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-532778907/5000000000 : ℝ)|^5663 ≤ (3250102586163/50000000000000 : ℝ)^4639
        have hw : |(-532778907/5000000000 : ℝ)|=(532778907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5499709383/10000000000 : ℝ)|^5663 ≤ (48197338331111/100000000000000 : ℝ)^4639
        have hw : |(5499709383/10000000000 : ℝ)|=(5499709383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_s2_6 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (326725353/625000000 : ℝ)*x 0 + (2749854641/5000000000 : ℝ)*x 1 + (-213111559/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (326725353/625000000 : ℝ)^5663 ≤ (453024577051/1000000000000 : ℝ)^4639 := by
    have hnat : (326725353 : ℕ)^5663*1000000000000^4639 ≤ 453024577051^4639*625000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326725353 625000000 453024577051 1000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2749854641/5000000000 : ℝ)^5663 ≤ (24098668625303/50000000000000 : ℝ)^4639 := by
    have hnat : (2749854641 : ℕ)^5663*50000000000000^4639 ≤ 24098668625303^4639*5000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2749854641 5000000000 24098668625303 50000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (213111559/2000000000 : ℝ)^5663 ≤ (1625051257709/25000000000000 : ℝ)^4639 := by
    have hnat : (213111559 : ℕ)^5663*25000000000000^4639 ≤ 1625051257709^4639*2000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213111559 2000000000 1625051257709 25000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(326725353/625000000 : ℝ), (2749854641/5000000000 : ℝ), (-213111559/2000000000 : ℝ)] ![(453024577051/1000000000000 : ℝ), (24098668625303/50000000000000 : ℝ), (1625051257709/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(326725353/625000000 : ℝ)|^5663 ≤ (453024577051/1000000000000 : ℝ)^4639
        have hw : |(326725353/625000000 : ℝ)|=(326725353/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2749854641/5000000000 : ℝ)|^5663 ≤ (24098668625303/50000000000000 : ℝ)^4639
        have hw : |(2749854641/5000000000 : ℝ)|=(2749854641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-213111559/2000000000 : ℝ)|^5663 ≤ (1625051257709/25000000000000 : ℝ)^4639
        have hw : |(-213111559/2000000000 : ℝ)|=(213111559/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1743_s2_7 (p : ℝ) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4036909997/10000000000 : ℝ)*x 0 + (4729157857/10000000000 : ℝ)*x 1 + (3407750067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4036909997/10000000000 : ℝ)^5663 ≤ (33043757782451/100000000000000 : ℝ)^4639 := by
    have hnat : (4036909997 : ℕ)^5663*100000000000000^4639 ≤ 33043757782451^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4036909997 10000000000 33043757782451 100000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4729157857/10000000000 : ℝ)^5663 ≤ (20043173924457/50000000000000 : ℝ)^4639 := by
    have hnat : (4729157857 : ℕ)^5663*50000000000000^4639 ≤ 20043173924457^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4729157857 10000000000 20043173924457 50000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3407750067/10000000000 : ℝ)^5663 ≤ (6717473588631/25000000000000 : ℝ)^4639 := by
    have hnat : (3407750067 : ℕ)^5663*25000000000000^4639 ≤ 6717473588631^4639*10000000000^5663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3407750067 10000000000 6717473588631 25000000000000 5663 4639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5663/1024 : ℝ)) 5663 4639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4036909997/10000000000 : ℝ), (4729157857/10000000000 : ℝ), (3407750067/10000000000 : ℝ)] ![(33043757782451/100000000000000 : ℝ), (20043173924457/50000000000000 : ℝ), (6717473588631/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4036909997/10000000000 : ℝ)|^5663 ≤ (33043757782451/100000000000000 : ℝ)^4639
        have hw : |(4036909997/10000000000 : ℝ)|=(4036909997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4729157857/10000000000 : ℝ)|^5663 ≤ (20043173924457/50000000000000 : ℝ)^4639
        have hw : |(4729157857/10000000000 : ℝ)|=(4729157857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3407750067/10000000000 : ℝ)|^5663 ≤ (6717473588631/25000000000000 : ℝ)^4639
        have hw : |(3407750067/10000000000 : ℝ)|=(3407750067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1743_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (52398121/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18209/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1773/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (8943/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9057/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18209/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1773/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18209/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1773/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18209/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1773/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18209/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1773/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18209/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1773/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18209/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1773/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1773/20000 : ℝ) ^ (5647/1024 : ℝ) ≤ (39333103610179/25000000000000000000 : ℝ) := by
    have hpowers : (1773/20000 : ℝ)^5647 ≤ (39333103610179/25000000000000000000 : ℝ)^1024 := by
      have hnat : (1773 : ℕ)^5647*25000000000000000000^1024 ≤ 39333103610179^1024*20000^5647 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1773 20000 39333103610179 25000000000000000000 5647 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1773/20000 : ℝ)) (X := (39333103610179/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5647 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18209/100000 : ℝ) ^ (5647/1024 : ℝ) ≤ (4165890774071621/50000000000000000000 : ℝ) := by
    have hpowers : (18209/100000 : ℝ)^5647 ≤ (4165890774071621/50000000000000000000 : ℝ)^1024 := by
      have hnat : (18209 : ℕ)^5647*50000000000000000000^1024 ≤ 4165890774071621^1024*100000^5647 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18209 100000 4165890774071621 50000000000000000000 5647 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18209/100000 : ℝ)) (X := (4165890774071621/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5647 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500039333103610179/12500000000000000000 : ℝ) ≤ (10000005705974319/10000000000000000 : ℝ) ^ (5647/1024 : ℝ) := by
    have hpowers : (12500039333103610179/12500000000000000000 : ℝ)^1024 ≤ (10000005705974319/10000000000000000 : ℝ)^5647 := by
      have hnat : (12500039333103610179 : ℕ)^1024*10000000000000000^5647 ≤ 10000005705974319^5647*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500039333103610179 12500000000000000000 10000005705974319 10000000000000000 1024 5647 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000005705974319/10000000000000000 : ℝ)) (X := (12500039333103610179/12500000000000000000 : ℝ)) (by norm_num) 5647 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50004244556981291979/50000000000000000000 : ℝ) ≤ (2500038483046963/2500000000000000 : ℝ) ^ (5647/1024 : ℝ) := by
    have hpowers : (50004244556981291979/50000000000000000000 : ℝ)^1024 ≤ (2500038483046963/2500000000000000 : ℝ)^5647 := by
      have hnat : (50004244556981291979 : ℕ)^1024*2500000000000000^5647 ≤ 2500038483046963^5647*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004244556981291979 50000000000000000000 2500038483046963 2500000000000000 1024 5647 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500038483046963/2500000000000000 : ℝ)) (X := (50004244556981291979/50000000000000000000 : ℝ)) (by norm_num) 5647 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25004165890774071621/25000000000000000000 : ℝ) ≤ (2000060431680277/2000000000000000 : ℝ) ^ (5647/1024 : ℝ) := by
    have hpowers : (25004165890774071621/25000000000000000000 : ℝ)^1024 ≤ (2000060431680277/2000000000000000 : ℝ)^5647 := by
      have hnat : (25004165890774071621 : ℕ)^1024*2000000000000000^5647 ≤ 2000060431680277^5647*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004165890774071621 25000000000000000000 2000060431680277 2000000000000000 1024 5647 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000060431680277/2000000000000000 : ℝ)) (X := (25004165890774071621/25000000000000000000 : ℝ)) (by norm_num) 5647 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(39333103610179/25000000000000000000 : ℝ) ≤ ((46718712632929048323/46720000000000000000 : ℝ)+2*(148226213533/934400000000000 : ℝ)*(1773/20000 : ℝ))^(5647/1024 : ℝ) := by
    rw [show (46718712632929048323/46720000000000000000 : ℝ)+2*(148226213533/934400000000000 : ℝ)*(1773/20000 : ℝ)=(10000005705974319/10000000000000000 : ℝ) by norm_num, show 1+2*(39333103610179/25000000000000000000 : ℝ)=(12500039333103610179/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4165890774071621/50000000000000000000 : ℝ)+(39333103610179/25000000000000000000 : ℝ) ≤ ((46718712632929048323/46720000000000000000 : ℝ)+(148226213533/934400000000000 : ℝ)*((18209/100000 : ℝ)+(1773/20000 : ℝ)))^(5647/1024 : ℝ) := by
    rw [show (46718712632929048323/46720000000000000000 : ℝ)+(148226213533/934400000000000 : ℝ)*((18209/100000 : ℝ)+(1773/20000 : ℝ))=(2500038483046963/2500000000000000 : ℝ) by norm_num, show 1+(4165890774071621/50000000000000000000 : ℝ)+(39333103610179/25000000000000000000 : ℝ)=(50004244556981291979/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4165890774071621/50000000000000000000 : ℝ) ≤ ((46718712632929048323/46720000000000000000 : ℝ)+2*(148226213533/934400000000000 : ℝ)*(18209/100000 : ℝ))^(5647/1024 : ℝ) := by
    rw [show (46718712632929048323/46720000000000000000 : ℝ)+2*(148226213533/934400000000000 : ℝ)*(18209/100000 : ℝ)=(2000060431680277/2000000000000000 : ℝ) by norm_num, show 1+2*(4165890774071621/50000000000000000000 : ℝ)=(25004165890774071621/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (46718712632929048323/46720000000000000000 : ℝ)*(X 1 0+X 2 0)+(148226213533/934400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5647/1024 : ℝ)) (lo := (1773/20000 : ℝ)) (hi := (18209/100000 : ℝ)) (c := (46718712632929048323/46720000000000000000 : ℝ)) (alpha := (148226213533/934400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (46718712632929048323/46720000000000000000 : ℝ)*(X 0 1+X 2 1)+(148226213533/934400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5647/1024 : ℝ)) (lo := (1773/20000 : ℝ)) (hi := (18209/100000 : ℝ)) (c := (46718712632929048323/46720000000000000000 : ℝ)) (alpha := (148226213533/934400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (46718712632929048323/46720000000000000000 : ℝ)*(X 0 2+X 1 2)+(148226213533/934400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5647/1024 : ℝ)) (lo := (1773/20000 : ℝ)) (hi := (18209/100000 : ℝ)) (c := (46718712632929048323/46720000000000000000 : ℝ)) (alpha := (148226213533/934400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-631153027/5000000000 : ℝ)*X 0 0+(5506737133/10000000000 : ℝ)*X 0 1+(2539416087/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5341232859/10000000000 : ℝ)*X 1 0+(-1486434737/10000000000 : ℝ)*X 1 1+(634853953/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5341232033/10000000000 : ℝ)*X 2 0+(2539416037/5000000000 : ℝ)*X 2 1+(-743217621/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((807148131/2000000000 : ℝ)*X 0 0+(1692659299/5000000000 : ℝ)*X 0 1+(593890847/1250000000 : ℝ)*X 0 2+(807148131/2000000000 : ℝ)*X 1 0+(1692659299/5000000000 : ℝ)*X 1 1+(593890847/1250000000 : ℝ)*X 1 2+(807148131/2000000000 : ℝ)*X 2 0+(1692659299/5000000000 : ℝ)*X 2 1+(593890847/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1262672443/10000000000 : ℝ)*X 0 0+(2542857503/5000000000 : ℝ)*X 0 1+(1374927353/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1306901383/2500000000 : ℝ)*X 1 0+(-532778907/5000000000 : ℝ)*X 1 1+(5499709383/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((326725353/625000000 : ℝ)*X 2 0+(2749854641/5000000000 : ℝ)*X 2 1+(-213111559/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4036909997/10000000000 : ℝ)*X 0 0+(4729157857/10000000000 : ℝ)*X 0 1+(3407750067/10000000000 : ℝ)*X 0 2+(4036909997/10000000000 : ℝ)*X 1 0+(4729157857/10000000000 : ℝ)*X 1 1+(3407750067/10000000000 : ℝ)*X 1 2+(4036909997/10000000000 : ℝ)*X 2 0+(4729157857/10000000000 : ℝ)*X 2 1+(3407750067/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1743_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10251825602995553240451970713/1168000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1660970989/100000000000000 : ℝ)*(base19) + (250288713/20000000000000 : ℝ)*(base23) + (25702969/100000000000000 : ℝ)*(lower2) + (7091083/2000000000000 : ℝ)*(upper3) + (20796423/100000000000000 : ℝ)*(upper5) + (767290725881659/50000000000000 : ℝ)*(major0) + (767290725881659/50000000000000 : ℝ)*(major1) + (767290725881659/50000000000000 : ℝ)*(major2) + (1168490386939431/50000000000000 : ℝ)*(sp0) + (1168493527959533/50000000000000 : ℝ)*(sp1) + (233698746544649/10000000000000 : ℝ)*(sp2) + (45760620890131/6250000000000 : ℝ)*(sp3) + (7943011193/100000000000000 : ℝ)*(sp4) + (494977443/12500000000000 : ℝ)*(sp7) + (732173894061639/100000000000000 : ℝ)*(f.failure) + (1168494358445027/50000000000000 : ℝ)*(f.sum) + (18204520644113/23360000000000000000000000000 : ℝ)*base66 + (28171431378567242143/2336000000000000000000000000000000 : ℝ)*base68 + (17825107571975242143/2336000000000000000000000000000000 : ℝ)*base70 + (19040429077959242143/2336000000000000000000000000000000 : ℝ)*base72 + (152472048781393/23360000000000000000000000000 : ℝ)*base74 + (12961061928455242143/2336000000000000000000000000000000 : ℝ)*base76 + (12666943853895242143/2336000000000000000000000000000000 : ℝ)*base78 + (21764894043783242143/2336000000000000000000000000000000 : ℝ)*base80 + (51430900771793/23360000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (8219681/2500000000000000000000 : ℝ)*base90 + (8219681/2500000000000000000000 : ℝ)*base92 + (8219681/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1431212368058231270190750441/292000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (343297131/50000000000000 : ℝ)*(base19) + (742741557/100000000000000 : ℝ)*(base23) + (100458899/100000000000000 : ℝ)*(upper3) + (20799/100000000000000 : ℝ)*(lower4) + (51284463/50000000000000 : ℝ)*(upper5) + (198266285717889/12500000000000 : ℝ)*(major0) + (198266285717889/12500000000000 : ℝ)*(major1) + (198266285717889/12500000000000 : ℝ)*(major2) + (4788172877/100000000000000 : ℝ)*(sp1) + (4903599187/100000000000000 : ℝ)*(sp2) + (1207745861381747/50000000000000 : ℝ)*(sp4) + (483097249599271/20000000000000 : ℝ)*(sp5) + (9661944305691/400000000000 : ℝ)*(sp6) + (9459608566779/1250000000000 : ℝ)*(sp7) + (9459608566779/1250000000000 : ℝ)*(f.failure) + (1207745861381747/50000000000000 : ℝ)*(f.sum) + (15679554844483/5840000000000000000000000000 : ℝ)*base66 + (2262476356082400147/584000000000000000000000000000000 : ℝ)*base67 + (3029464034093599853/584000000000000000000000000000000 : ℝ)*base70 + (1297397866693599853/584000000000000000000000000000000 : ℝ)*base72 + (13404610373197/5840000000000000000000000000 : ℝ)*base73 + (9106954133599853/584000000000000000000000000000000 : ℝ)*base76 + (95998119994400147/584000000000000000000000000000000 : ℝ)*base77 + (822269094333599853/584000000000000000000000000000000 : ℝ)*base80 + (29846073474403/5840000000000000000000000000 : ℝ)*base82 + (122259/31250000000000000000 : ℝ)*base89 + (122259/31250000000000000000 : ℝ)*base91 + (122259/31250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1743_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (52398121/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18209/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1773/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8943/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9057/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1743_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1743_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (52398121/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8943/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9057/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1743_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1743_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1743_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5647/1024 : ℝ) ≤ p) (hpb : p ≤ (5663/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (52398121/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8943/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9057/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1743_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

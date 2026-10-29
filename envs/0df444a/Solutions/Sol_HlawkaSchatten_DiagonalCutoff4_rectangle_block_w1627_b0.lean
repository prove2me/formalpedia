-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1627_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:59:10.758934+00:00
-- url     : https://prove2.me/submissions/b37a0313-b4e3-422f-b55f-9ce2666fadc6

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
theorem support_rectangle_w1627_s0_0 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1533887759/10000000000 : ℝ)*x 0 + (5814531729/10000000000 : ℝ)*x 1 + (76648217/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1533887759/10000000000 : ℝ)^4827 ≤ (231472534309/2500000000000 : ℝ)^3803 := by
    have hnat : (1533887759 : ℕ)^4827*2500000000000^3803 ≤ 231472534309^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1533887759 10000000000 231472534309 2500000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5814531729/10000000000 : ℝ)^4827 ≤ (50246720741909/100000000000000 : ℝ)^3803 := by
    have hnat : (5814531729 : ℕ)^4827*100000000000000^3803 ≤ 50246720741909^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5814531729 10000000000 50246720741909 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (76648217/156250000 : ℝ)^4827 ≤ (20247188930359/50000000000000 : ℝ)^3803 := by
    have hnat : (76648217 : ℕ)^4827*50000000000000^3803 ≤ 20247188930359^3803*156250000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76648217 156250000 20247188930359 50000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1533887759/10000000000 : ℝ), (5814531729/10000000000 : ℝ), (76648217/156250000 : ℝ)] ![(231472534309/2500000000000 : ℝ), (50246720741909/100000000000000 : ℝ), (20247188930359/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1533887759/10000000000 : ℝ)|^4827 ≤ (231472534309/2500000000000 : ℝ)^3803
        have hw : |(-1533887759/10000000000 : ℝ)|=(1533887759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5814531729/10000000000 : ℝ)|^4827 ≤ (50246720741909/100000000000000 : ℝ)^3803
        have hw : |(5814531729/10000000000 : ℝ)|=(5814531729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(76648217/156250000 : ℝ)|^4827 ≤ (20247188930359/50000000000000 : ℝ)^3803
        have hw : |(76648217/156250000 : ℝ)|=(76648217/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s0_1 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2723381971/5000000000 : ℝ)*x 0 + (-1017656181/5000000000 : ℝ)*x 1 + (2452743537/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2723381971/5000000000 : ℝ)^4827 ≤ (722621624867/1562500000000 : ℝ)^3803 := by
    have hnat : (2723381971 : ℕ)^4827*1562500000000^3803 ≤ 722621624867^3803*5000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2723381971 5000000000 722621624867 1562500000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1017656181/5000000000 : ℝ)^4827 ≤ (13257825705427/100000000000000 : ℝ)^3803 := by
    have hnat : (1017656181 : ℕ)^4827*100000000000000^3803 ≤ 13257825705427^3803*5000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1017656181 5000000000 13257825705427 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2452743537/5000000000 : ℝ)^4827 ≤ (20247195143603/50000000000000 : ℝ)^3803 := by
    have hnat : (2452743537 : ℕ)^4827*50000000000000^3803 ≤ 20247195143603^3803*5000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2452743537 5000000000 20247195143603 50000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2723381971/5000000000 : ℝ), (-1017656181/5000000000 : ℝ), (2452743537/5000000000 : ℝ)] ![(722621624867/1562500000000 : ℝ), (13257825705427/100000000000000 : ℝ), (20247195143603/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2723381971/5000000000 : ℝ)|^4827 ≤ (722621624867/1562500000000 : ℝ)^3803
        have hw : |(2723381971/5000000000 : ℝ)|=(2723381971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1017656181/5000000000 : ℝ)|^4827 ≤ (13257825705427/100000000000000 : ℝ)^3803
        have hw : |(-1017656181/5000000000 : ℝ)|=(1017656181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2452743537/5000000000 : ℝ)|^4827 ≤ (20247195143603/50000000000000 : ℝ)^3803
        have hw : |(2452743537/5000000000 : ℝ)|=(2452743537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s0_2 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5446763863/10000000000 : ℝ)*x 0 + (4905486369/10000000000 : ℝ)*x 1 + (-1017656679/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5446763863/10000000000 : ℝ)^4827 ≤ (23123891570047/50000000000000 : ℝ)^3803 := by
    have hnat : (5446763863 : ℕ)^4827*50000000000000^3803 ≤ 23123891570047^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5446763863 10000000000 23123891570047 50000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4905486369/10000000000 : ℝ)^4827 ≤ (20247191450233/50000000000000 : ℝ)^3803 := by
    have hnat : (4905486369 : ℕ)^4827*50000000000000^3803 ≤ 20247191450233^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4905486369 10000000000 20247191450233 50000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1017656679/5000000000 : ℝ)^4827 ≤ (13257833940199/100000000000000 : ℝ)^3803 := by
    have hnat : (1017656679 : ℕ)^4827*100000000000000^3803 ≤ 13257833940199^3803*5000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1017656679 5000000000 13257833940199 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5446763863/10000000000 : ℝ), (4905486369/10000000000 : ℝ), (-1017656679/5000000000 : ℝ)] ![(23123891570047/50000000000000 : ℝ), (20247191450233/50000000000000 : ℝ), (13257833940199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5446763863/10000000000 : ℝ)|^4827 ≤ (23123891570047/50000000000000 : ℝ)^3803
        have hw : |(5446763863/10000000000 : ℝ)|=(5446763863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4905486369/10000000000 : ℝ)|^4827 ≤ (20247191450233/50000000000000 : ℝ)^3803
        have hw : |(4905486369/10000000000 : ℝ)|=(4905486369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1017656679/5000000000 : ℝ)|^4827 ≤ (13257833940199/100000000000000 : ℝ)^3803
        have hw : |(-1017656679/5000000000 : ℝ)|=(1017656679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s0_3 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (12817261/31250000 : ℝ)*x 0 + (615480857/2000000000 : ℝ)*x 1 + (2680663329/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (12817261/31250000 : ℝ)^4827 ≤ (32264608750327/100000000000000 : ℝ)^3803 := by
    have hnat : (12817261 : ℕ)^4827*100000000000000^3803 ≤ 32264608750327^3803*31250000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12817261 31250000 32264608750327 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (615480857/2000000000 : ℝ)^4827 ≤ (22406424482471/100000000000000 : ℝ)^3803 := by
    have hnat : (615480857 : ℕ)^4827*100000000000000^3803 ≤ 22406424482471^3803*2000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      615480857 2000000000 22406424482471 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2680663329/5000000000 : ℝ)^4827 ≤ (45328966755267/100000000000000 : ℝ)^3803 := by
    have hnat : (2680663329 : ℕ)^4827*100000000000000^3803 ≤ 45328966755267^3803*5000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680663329 5000000000 45328966755267 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(12817261/31250000 : ℝ), (615480857/2000000000 : ℝ), (2680663329/5000000000 : ℝ)] ![(32264608750327/100000000000000 : ℝ), (22406424482471/100000000000000 : ℝ), (45328966755267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(12817261/31250000 : ℝ)|^4827 ≤ (32264608750327/100000000000000 : ℝ)^3803
        have hw : |(12817261/31250000 : ℝ)|=(12817261/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(615480857/2000000000 : ℝ)|^4827 ≤ (22406424482471/100000000000000 : ℝ)^3803
        have hw : |(615480857/2000000000 : ℝ)|=(615480857/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2680663329/5000000000 : ℝ)|^4827 ≤ (45328966755267/100000000000000 : ℝ)^3803
        have hw : |(2680663329/5000000000 : ℝ)|=(2680663329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s0_4 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1536458297/10000000000 : ℝ)*x 0 + (30801917/62500000 : ℝ)*x 1 + (180965921/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1536458297/10000000000 : ℝ)^4827 ≤ (4639300064429/50000000000000 : ℝ)^3803 := by
    have hnat : (1536458297 : ℕ)^4827*50000000000000^3803 ≤ 4639300064429^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1536458297 10000000000 4639300064429 50000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (30801917/62500000 : ℝ)^4827 ≤ (40733636021741/100000000000000 : ℝ)^3803 := by
    have hnat : (30801917 : ℕ)^4827*100000000000000^3803 ≤ 40733636021741^3803*62500000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30801917 62500000 40733636021741 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (180965921/312500000 : ℝ)^4827 ≤ (49987763832633/100000000000000 : ℝ)^3803 := by
    have hnat : (180965921 : ℕ)^4827*100000000000000^3803 ≤ 49987763832633^3803*312500000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180965921 312500000 49987763832633 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1536458297/10000000000 : ℝ), (30801917/62500000 : ℝ), (180965921/312500000 : ℝ)] ![(4639300064429/50000000000000 : ℝ), (40733636021741/100000000000000 : ℝ), (49987763832633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1536458297/10000000000 : ℝ)|^4827 ≤ (4639300064429/50000000000000 : ℝ)^3803
        have hw : |(-1536458297/10000000000 : ℝ)|=(1536458297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(30801917/62500000 : ℝ)|^4827 ≤ (40733636021741/100000000000000 : ℝ)^3803
        have hw : |(30801917/62500000 : ℝ)|=(30801917/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(180965921/312500000 : ℝ)|^4827 ≤ (49987763832633/100000000000000 : ℝ)^3803
        have hw : |(180965921/312500000 : ℝ)|=(180965921/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s0_5 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5198554231/10000000000 : ℝ)*x 0 + (-1149889523/10000000000 : ℝ)*x 1 + (5790909573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5198554231/10000000000 : ℝ)^4827 ≤ (21794695769657/50000000000000 : ℝ)^3803 := by
    have hnat : (5198554231 : ℕ)^4827*50000000000000^3803 ≤ 21794695769657^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5198554231 10000000000 21794695769657 50000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1149889523/10000000000 : ℝ)^4827 ≤ (256913740393/4000000000000 : ℝ)^3803 := by
    have hnat : (1149889523 : ℕ)^4827*4000000000000^3803 ≤ 256913740393^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1149889523 10000000000 256913740393 4000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5790909573/10000000000 : ℝ)^4827 ≤ (4998776493923/10000000000000 : ℝ)^3803 := by
    have hnat : (5790909573 : ℕ)^4827*10000000000000^3803 ≤ 4998776493923^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5790909573 10000000000 4998776493923 10000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5198554231/10000000000 : ℝ), (-1149889523/10000000000 : ℝ), (5790909573/10000000000 : ℝ)] ![(21794695769657/50000000000000 : ℝ), (256913740393/4000000000000 : ℝ), (4998776493923/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5198554231/10000000000 : ℝ)|^4827 ≤ (21794695769657/50000000000000 : ℝ)^3803
        have hw : |(5198554231/10000000000 : ℝ)|=(5198554231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1149889523/10000000000 : ℝ)|^4827 ≤ (256913740393/4000000000000 : ℝ)^3803
        have hw : |(-1149889523/10000000000 : ℝ)|=(1149889523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5790909573/10000000000 : ℝ)|^4827 ≤ (4998776493923/10000000000000 : ℝ)^3803
        have hw : |(5790909573/10000000000 : ℝ)|=(5790909573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s0_6 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2599277327/5000000000 : ℝ)*x 0 + (2895454503/5000000000 : ℝ)*x 1 + (-287472441/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2599277327/5000000000 : ℝ)^4827 ≤ (43589396041149/100000000000000 : ℝ)^3803 := by
    have hnat : (2599277327 : ℕ)^4827*100000000000000^3803 ≤ 43589396041149^3803*5000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2599277327 5000000000 43589396041149 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2895454503/5000000000 : ℝ)^4827 ≤ (49987758726951/100000000000000 : ℝ)^3803 := by
    have hnat : (2895454503 : ℕ)^4827*100000000000000^3803 ≤ 49987758726951^3803*5000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2895454503 5000000000 49987758726951 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (287472441/2500000000 : ℝ)^4827 ≤ (321142260921/5000000000000 : ℝ)^3803 := by
    have hnat : (287472441 : ℕ)^4827*5000000000000^3803 ≤ 321142260921^3803*2500000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287472441 2500000000 321142260921 5000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2599277327/5000000000 : ℝ), (2895454503/5000000000 : ℝ), (-287472441/2500000000 : ℝ)] ![(43589396041149/100000000000000 : ℝ), (49987758726951/100000000000000 : ℝ), (321142260921/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2599277327/5000000000 : ℝ)|^4827 ≤ (43589396041149/100000000000000 : ℝ)^3803
        have hw : |(2599277327/5000000000 : ℝ)|=(2599277327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2895454503/5000000000 : ℝ)|^4827 ≤ (49987758726951/100000000000000 : ℝ)^3803
        have hw : |(2895454503/5000000000 : ℝ)|=(2895454503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-287472441/2500000000 : ℝ)|^4827 ≤ (321142260921/5000000000000 : ℝ)^3803
        have hw : |(-287472441/2500000000 : ℝ)|=(287472441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s0_7 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (205399243/500000000 : ℝ)*x 0 + (5303988653/10000000000 : ℝ)*x 1 + (3136754531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (205399243/500000000 : ℝ)^4827 ≤ (8082284136493/25000000000000 : ℝ)^3803 := by
    have hnat : (205399243 : ℕ)^4827*25000000000000^3803 ≤ 8082284136493^3803*500000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205399243 500000000 8082284136493 25000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5303988653/10000000000 : ℝ)^4827 ≤ (11178635148613/25000000000000 : ℝ)^3803 := by
    have hnat : (5303988653 : ℕ)^4827*25000000000000^3803 ≤ 11178635148613^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303988653 10000000000 11178635148613 25000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3136754531/10000000000 : ℝ)^4827 ≤ (22956322848011/100000000000000 : ℝ)^3803 := by
    have hnat : (3136754531 : ℕ)^4827*100000000000000^3803 ≤ 22956322848011^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3136754531 10000000000 22956322848011 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(205399243/500000000 : ℝ), (5303988653/10000000000 : ℝ), (3136754531/10000000000 : ℝ)] ![(8082284136493/25000000000000 : ℝ), (11178635148613/25000000000000 : ℝ), (22956322848011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(205399243/500000000 : ℝ)|^4827 ≤ (8082284136493/25000000000000 : ℝ)^3803
        have hw : |(205399243/500000000 : ℝ)|=(205399243/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5303988653/10000000000 : ℝ)|^4827 ≤ (11178635148613/25000000000000 : ℝ)^3803
        have hw : |(5303988653/10000000000 : ℝ)|=(5303988653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3136754531/10000000000 : ℝ)|^4827 ≤ (22956322848011/100000000000000 : ℝ)^3803
        have hw : |(3136754531/10000000000 : ℝ)|=(3136754531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1627_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175621841/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (4383/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (23857/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4823/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4823 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4823*1^1024 ≤ 0^1024*1^4823 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4823 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4823 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4823/1024 : ℝ) ≤ (1335728226933905257/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4823 ≤ (1335728226933905257/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4823*100000000000000000000^1024 ≤ 1335728226933905257^1024*5^4823 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1335728226933905257 100000000000000000000 4823 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1335728226933905257/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4823 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4823/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4823 := by
      have hnat : (1 : ℕ)^1024*1^4823 ≤ 1^4823*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4823 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4823 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101335728226933905257/100000000000000000000 : ℝ) ≤ (10028211631661729/10000000000000000 : ℝ) ^ (4823/1024 : ℝ) := by
    have hpowers : (101335728226933905257/100000000000000000000 : ℝ)^1024 ≤ (10028211631661729/10000000000000000 : ℝ)^4823 := by
      have hnat : (101335728226933905257 : ℕ)^1024*10000000000000000^4823 ≤ 10028211631661729^4823*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101335728226933905257 100000000000000000000 10028211631661729 10000000000000000 1024 4823 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10028211631661729/10000000000000000 : ℝ)) (X := (101335728226933905257/100000000000000000000 : ℝ)) (by norm_num) 4823 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51335728226933905257/50000000000000000000 : ℝ) ≤ (5028211631661729/5000000000000000 : ℝ) ^ (4823/1024 : ℝ) := by
    have hpowers : (51335728226933905257/50000000000000000000 : ℝ)^1024 ≤ (5028211631661729/5000000000000000 : ℝ)^4823 := by
      have hnat : (51335728226933905257 : ℕ)^1024*5000000000000000^4823 ≤ 5028211631661729^4823*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51335728226933905257 50000000000000000000 5028211631661729 5000000000000000 1024 4823 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5028211631661729/5000000000000000 : ℝ)) (X := (51335728226933905257/50000000000000000000 : ℝ)) (by norm_num) 4823 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(28211631661729/4000000000000000 : ℝ)*(0 : ℝ))^(4823/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(28211631661729/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1335728226933905257/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(28211631661729/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4823/1024 : ℝ) := by
    rw [show (1 : ℝ)+(28211631661729/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10028211631661729/10000000000000000 : ℝ) by norm_num, show 1+(1335728226933905257/100000000000000000000 : ℝ)+(0 : ℝ)=(101335728226933905257/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1335728226933905257/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(28211631661729/4000000000000000 : ℝ)*(2/5 : ℝ))^(4823/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(28211631661729/4000000000000000 : ℝ)*(2/5 : ℝ)=(5028211631661729/5000000000000000 : ℝ) by norm_num, show 1+2*(1335728226933905257/100000000000000000000 : ℝ)=(51335728226933905257/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(28211631661729/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4823/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28211631661729/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(28211631661729/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4823/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28211631661729/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(28211631661729/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4823/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28211631661729/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1533887759/10000000000 : ℝ)*X 0 0+(5814531729/10000000000 : ℝ)*X 0 1+(76648217/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2723381971/5000000000 : ℝ)*X 1 0+(-1017656181/5000000000 : ℝ)*X 1 1+(2452743537/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5446763863/10000000000 : ℝ)*X 2 0+(4905486369/10000000000 : ℝ)*X 2 1+(-1017656679/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((12817261/31250000 : ℝ)*X 0 0+(615480857/2000000000 : ℝ)*X 0 1+(2680663329/5000000000 : ℝ)*X 0 2+(12817261/31250000 : ℝ)*X 1 0+(615480857/2000000000 : ℝ)*X 1 1+(2680663329/5000000000 : ℝ)*X 1 2+(12817261/31250000 : ℝ)*X 2 0+(615480857/2000000000 : ℝ)*X 2 1+(2680663329/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1536458297/10000000000 : ℝ)*X 0 0+(30801917/62500000 : ℝ)*X 0 1+(180965921/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5198554231/10000000000 : ℝ)*X 1 0+(-1149889523/10000000000 : ℝ)*X 1 1+(5790909573/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2599277327/5000000000 : ℝ)*X 2 0+(2895454503/5000000000 : ℝ)*X 2 1+(-287472441/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((205399243/500000000 : ℝ)*X 0 0+(5303988653/10000000000 : ℝ)*X 0 1+(3136754531/10000000000 : ℝ)*X 0 2+(205399243/500000000 : ℝ)*X 1 0+(5303988653/10000000000 : ℝ)*X 1 1+(3136754531/10000000000 : ℝ)*X 1 2+(205399243/500000000 : ℝ)*X 2 0+(5303988653/10000000000 : ℝ)*X 2 1+(3136754531/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1638339036178163211/200000000000000000000000 : ℝ) := by norm_num
    linear_combination (78455251/5000000000000 : ℝ)*(base19) + (1511284629/100000000000000 : ℝ)*(base23) + (50688459/12500000000000 : ℝ)*(upper3) + (22802869/100000000000000 : ℝ)*(upper4) + (40132261/100000000000000 : ℝ)*(upper5) + (768959343074707/100000000000000 : ℝ)*(major0) + (768959343074707/100000000000000 : ℝ)*(major1) + (768959343074707/100000000000000 : ℝ)*(major2) + (1100062996632691/100000000000000 : ℝ)*(sp0) + (110006734947387/10000000000000 : ℝ)*(sp1) + (55003370364713/5000000000000 : ℝ)*(sp2) + (437845743369401/100000000000000 : ℝ)*(sp3) + (2960973099/50000000000000 : ℝ)*(sp4) + (1875572307/50000000000000 : ℝ)*(sp7) + (87569898902803/20000000000000 : ℝ)*(f.failure) + (1100068918578889/100000000000000 : ℝ)*(f.sum) + (539746342788403/200000000000000000000000000000 : ℝ)*base65 + (555109989388403/400000000000000000000000000000 : ℝ)*base67 + (2709985382611597/400000000000000000000000000000 : ℝ)*base70 + (71369840211597/400000000000000000000000000000 : ℝ)*base72 + (419177142388403/200000000000000000000000000000 : ℝ)*base73 + (3547267109011597/400000000000000000000000000000 : ℝ)*base76 + (146622176211597/400000000000000000000000000000 : ℝ)*base78 + (1138334532988403/400000000000000000000000000000 : ℝ)*base79 + (605311962611597/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2920323/2000000000000000000000 : ℝ)*base89 + (2920323/2000000000000000000000 : ℝ)*base91 + (2920323/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (868201887025893679624713/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (47501183/5000000000000 : ℝ)*(base19) + (42055431/4000000000000 : ℝ)*(base23) + (45143419/20000000000000 : ℝ)*(base32) + (10874807/6250000000000 : ℝ)*(upper3) + (12987507/20000000000000 : ℝ)*(upper5) + (810349323817699/100000000000000 : ℝ)*(major0) + (810349323817699/100000000000000 : ℝ)*(major1) + (810349323817699/100000000000000 : ℝ)*(major2) + (1341649773/50000000000000 : ℝ)*(sp1) + (1415301831/50000000000000 : ℝ)*(sp2) + (1159281335683257/100000000000000 : ℝ)*(sp4) + (23185554047201/2000000000000 : ℝ)*(sp5) + (57963872684691/5000000000000 : ℝ)*(sp6) + (461416941534727/100000000000000 : ℝ)*(sp7) + (230708583625911/50000000000000 : ℝ)*(f.failure) + (1159281335683257/100000000000000 : ℝ)*(f.sum) + (176562347058429/200000000000000000000000000000 : ℝ)*base66 + (211941722741571/400000000000000000000000000000 : ℝ)*base67 + (542525705258429/400000000000000000000000000000 : ℝ)*base70 + (2870807590341571/400000000000000000000000000000 : ℝ)*base71 + (1041224154658429/200000000000000000000000000000 : ℝ)*base74 + (2554387594741571/400000000000000000000000000000 : ℝ)*base75 + (967422508741571/400000000000000000000000000000 : ℝ)*base77 + (642966059541571/400000000000000000000000000000 : ℝ)*base79 + (902986881058429/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (4877849/5000000000000000000000 : ℝ)*base90 + (4877849/5000000000000000000000 : ℝ)*base92 + (4877849/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1627_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175621841/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4383/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (23857/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1627_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1627_s1_0 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-824799563/5000000000 : ℝ)*x 0 + (5514687331/10000000000 : ℝ)*x 1 + (1026067973/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (824799563/5000000000 : ℝ)^4827 ≤ (10154273627927/100000000000000 : ℝ)^3803 := by
    have hnat : (824799563 : ℕ)^4827*100000000000000^3803 ≤ 10154273627927^3803*5000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      824799563 5000000000 10154273627927 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5514687331/10000000000 : ℝ)^4827 ≤ (46981028839141/100000000000000 : ℝ)^3803 := by
    have hnat : (5514687331 : ℕ)^4827*100000000000000^3803 ≤ 46981028839141^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5514687331 10000000000 46981028839141 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1026067973/2000000000 : ℝ)^4827 ≤ (42864697520377/100000000000000 : ℝ)^3803 := by
    have hnat : (1026067973 : ℕ)^4827*100000000000000^3803 ≤ 42864697520377^3803*2000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026067973 2000000000 42864697520377 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-824799563/5000000000 : ℝ), (5514687331/10000000000 : ℝ), (1026067973/2000000000 : ℝ)] ![(10154273627927/100000000000000 : ℝ), (46981028839141/100000000000000 : ℝ), (42864697520377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-824799563/5000000000 : ℝ)|^4827 ≤ (10154273627927/100000000000000 : ℝ)^3803
        have hw : |(-824799563/5000000000 : ℝ)|=(824799563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5514687331/10000000000 : ℝ)|^4827 ≤ (46981028839141/100000000000000 : ℝ)^3803
        have hw : |(5514687331/10000000000 : ℝ)|=(5514687331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1026067973/2000000000 : ℝ)|^4827 ≤ (42864697520377/100000000000000 : ℝ)^3803
        have hw : |(1026067973/2000000000 : ℝ)|=(1026067973/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s1_1 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1073400777/2000000000 : ℝ)*x 0 + (-925030917/5000000000 : ℝ)*x 1 + (2565169821/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073400777/2000000000 : ℝ)^4827 ≤ (45389899771663/100000000000000 : ℝ)^3803 := by
    have hnat : (1073400777 : ℕ)^4827*100000000000000^3803 ≤ 45389899771663^3803*2000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073400777 2000000000 45389899771663 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (925030917/5000000000 : ℝ)^4827 ≤ (11745405061403/100000000000000 : ℝ)^3803 := by
    have hnat : (925030917 : ℕ)^4827*100000000000000^3803 ≤ 11745405061403^3803*5000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      925030917 5000000000 11745405061403 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2565169821/5000000000 : ℝ)^4827 ≤ (8572939031099/20000000000000 : ℝ)^3803 := by
    have hnat : (2565169821 : ℕ)^4827*20000000000000^3803 ≤ 8572939031099^3803*5000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2565169821 5000000000 8572939031099 20000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073400777/2000000000 : ℝ), (-925030917/5000000000 : ℝ), (2565169821/5000000000 : ℝ)] ![(45389899771663/100000000000000 : ℝ), (11745405061403/100000000000000 : ℝ), (8572939031099/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073400777/2000000000 : ℝ)|^4827 ≤ (45389899771663/100000000000000 : ℝ)^3803
        have hw : |(1073400777/2000000000 : ℝ)|=(1073400777/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-925030917/5000000000 : ℝ)|^4827 ≤ (11745405061403/100000000000000 : ℝ)^3803
        have hw : |(-925030917/5000000000 : ℝ)|=(925030917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2565169821/5000000000 : ℝ)|^4827 ≤ (8572939031099/20000000000000 : ℝ)^3803
        have hw : |(2565169821/5000000000 : ℝ)|=(2565169821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s1_2 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5367004449/10000000000 : ℝ)*x 0 + (1282584731/2500000000 : ℝ)*x 1 + (-462515507/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5367004449/10000000000 : ℝ)^4827 ≤ (45389905825871/100000000000000 : ℝ)^3803 := by
    have hnat : (5367004449 : ℕ)^4827*100000000000000^3803 ≤ 45389905825871^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367004449 10000000000 45389905825871 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1282584731/2500000000 : ℝ)^4827 ≤ (10716171885303/25000000000000 : ℝ)^3803 := by
    have hnat : (1282584731 : ℕ)^4827*25000000000000^3803 ≤ 10716171885303^3803*2500000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1282584731 2500000000 10716171885303 25000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (462515507/2500000000 : ℝ)^4827 ≤ (469816264987/4000000000000 : ℝ)^3803 := by
    have hnat : (462515507 : ℕ)^4827*4000000000000^3803 ≤ 469816264987^3803*2500000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      462515507 2500000000 469816264987 4000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5367004449/10000000000 : ℝ), (1282584731/2500000000 : ℝ), (-462515507/2500000000 : ℝ)] ![(45389905825871/100000000000000 : ℝ), (10716171885303/25000000000000 : ℝ), (469816264987/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5367004449/10000000000 : ℝ)|^4827 ≤ (45389905825871/100000000000000 : ℝ)^3803
        have hw : |(5367004449/10000000000 : ℝ)|=(5367004449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1282584731/2500000000 : ℝ)|^4827 ≤ (10716171885303/25000000000000 : ℝ)^3803
        have hw : |(1282584731/2500000000 : ℝ)|=(1282584731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-462515507/2500000000 : ℝ)|^4827 ≤ (469816264987/4000000000000 : ℝ)^3803
        have hw : |(-462515507/2500000000 : ℝ)|=(462515507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s1_3 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (418932613/1000000000 : ℝ)*x 0 + (186366197/500000000 : ℝ)*x 1 + (4692974363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (418932613/1000000000 : ℝ)^4827 ≤ (4142974914279/12500000000000 : ℝ)^3803 := by
    have hnat : (418932613 : ℕ)^4827*12500000000000^3803 ≤ 4142974914279^3803*1000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418932613 1000000000 4142974914279 12500000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (186366197/500000000 : ℝ)^4827 ≤ (357191462307/1250000000000 : ℝ)^3803 := by
    have hnat : (186366197 : ℕ)^4827*1250000000000^3803 ≤ 357191462307^3803*500000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      186366197 500000000 357191462307 1250000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4692974363/10000000000 : ℝ)^4827 ≤ (38280883684443/100000000000000 : ℝ)^3803 := by
    have hnat : (4692974363 : ℕ)^4827*100000000000000^3803 ≤ 38280883684443^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4692974363 10000000000 38280883684443 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(418932613/1000000000 : ℝ), (186366197/500000000 : ℝ), (4692974363/10000000000 : ℝ)] ![(4142974914279/12500000000000 : ℝ), (357191462307/1250000000000 : ℝ), (38280883684443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(418932613/1000000000 : ℝ)|^4827 ≤ (4142974914279/12500000000000 : ℝ)^3803
        have hw : |(418932613/1000000000 : ℝ)|=(418932613/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(186366197/500000000 : ℝ)|^4827 ≤ (357191462307/1250000000000 : ℝ)^3803
        have hw : |(186366197/500000000 : ℝ)|=(186366197/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4692974363/10000000000 : ℝ)|^4827 ≤ (38280883684443/100000000000000 : ℝ)^3803
        have hw : |(4692974363/10000000000 : ℝ)|=(4692974363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s1_4 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-329957999/2000000000 : ℝ)*x 0 + (1026878651/2000000000 : ℝ)*x 1 + (1377643319/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329957999/2000000000 : ℝ)^4827 ≤ (634735307687/6250000000000 : ℝ)^3803 := by
    have hnat : (329957999 : ℕ)^4827*6250000000000^3803 ≤ 634735307687^3803*2000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329957999 2000000000 634735307687 6250000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1026878651/2000000000 : ℝ)^4827 ≤ (42907687691753/100000000000000 : ℝ)^3803 := by
    have hnat : (1026878651 : ℕ)^4827*100000000000000^3803 ≤ 42907687691753^3803*2000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026878651 2000000000 42907687691753 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1377643319/2500000000 : ℝ)^4827 ≤ (46936547375747/100000000000000 : ℝ)^3803 := by
    have hnat : (1377643319 : ℕ)^4827*100000000000000^3803 ≤ 46936547375747^3803*2500000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377643319 2500000000 46936547375747 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-329957999/2000000000 : ℝ), (1026878651/2000000000 : ℝ), (1377643319/2500000000 : ℝ)] ![(634735307687/6250000000000 : ℝ), (42907687691753/100000000000000 : ℝ), (46936547375747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-329957999/2000000000 : ℝ)|^4827 ≤ (634735307687/6250000000000 : ℝ)^3803
        have hw : |(-329957999/2000000000 : ℝ)|=(329957999/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1026878651/2000000000 : ℝ)|^4827 ≤ (42907687691753/100000000000000 : ℝ)^3803
        have hw : |(1026878651/2000000000 : ℝ)|=(1026878651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1377643319/2500000000 : ℝ)|^4827 ≤ (46936547375747/100000000000000 : ℝ)^3803
        have hw : |(1377643319/2500000000 : ℝ)|=(1377643319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s1_5 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2632256443/5000000000 : ℝ)*x 0 + (-1469827443/10000000000 : ℝ)*x 1 + (5510573619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2632256443/5000000000 : ℝ)^4827 ≤ (5536570111721/12500000000000 : ℝ)^3803 := by
    have hnat : (2632256443 : ℕ)^4827*12500000000000^3803 ≤ 5536570111721^3803*5000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632256443 5000000000 5536570111721 12500000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1469827443/10000000000 : ℝ)^4827 ≤ (8770888006339/100000000000000 : ℝ)^3803 := by
    have hnat : (1469827443 : ℕ)^4827*100000000000000^3803 ≤ 8770888006339^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1469827443 10000000000 8770888006339 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5510573619/10000000000 : ℝ)^4827 ≤ (9387310216783/20000000000000 : ℝ)^3803 := by
    have hnat : (5510573619 : ℕ)^4827*20000000000000^3803 ≤ 9387310216783^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510573619 10000000000 9387310216783 20000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2632256443/5000000000 : ℝ), (-1469827443/10000000000 : ℝ), (5510573619/10000000000 : ℝ)] ![(5536570111721/12500000000000 : ℝ), (8770888006339/100000000000000 : ℝ), (9387310216783/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2632256443/5000000000 : ℝ)|^4827 ≤ (5536570111721/12500000000000 : ℝ)^3803
        have hw : |(2632256443/5000000000 : ℝ)|=(2632256443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1469827443/10000000000 : ℝ)|^4827 ≤ (8770888006339/100000000000000 : ℝ)^3803
        have hw : |(-1469827443/10000000000 : ℝ)|=(1469827443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5510573619/10000000000 : ℝ)|^4827 ≤ (9387310216783/20000000000000 : ℝ)^3803
        have hw : |(5510573619/10000000000 : ℝ)|=(5510573619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s1_6 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1052902447/2000000000 : ℝ)*x 0 + (2755286929/5000000000 : ℝ)*x 1 + (-1469828019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052902447/2000000000 : ℝ)^4827 ≤ (44292553941851/100000000000000 : ℝ)^3803 := by
    have hnat : (1052902447 : ℕ)^4827*100000000000000^3803 ≤ 44292553941851^3803*2000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052902447 2000000000 44292553941851 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2755286929/5000000000 : ℝ)^4827 ≤ (46936553667741/100000000000000 : ℝ)^3803 := by
    have hnat : (2755286929 : ℕ)^4827*100000000000000^3803 ≤ 46936553667741^3803*5000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755286929 5000000000 46936553667741 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1469828019/10000000000 : ℝ)^4827 ≤ (274090386531/3125000000000 : ℝ)^3803 := by
    have hnat : (1469828019 : ℕ)^4827*3125000000000^3803 ≤ 274090386531^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1469828019 10000000000 274090386531 3125000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1052902447/2000000000 : ℝ), (2755286929/5000000000 : ℝ), (-1469828019/10000000000 : ℝ)] ![(44292553941851/100000000000000 : ℝ), (46936553667741/100000000000000 : ℝ), (274090386531/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1052902447/2000000000 : ℝ)|^4827 ≤ (44292553941851/100000000000000 : ℝ)^3803
        have hw : |(1052902447/2000000000 : ℝ)|=(1052902447/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2755286929/5000000000 : ℝ)|^4827 ≤ (46936553667741/100000000000000 : ℝ)^3803
        have hw : |(2755286929/5000000000 : ℝ)|=(2755286929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1469828019/10000000000 : ℝ)|^4827 ≤ (274090386531/3125000000000 : ℝ)^3803
        have hw : |(-1469828019/10000000000 : ℝ)|=(1469828019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s1_7 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4189803083/10000000000 : ℝ)*x 0 + (2341395671/5000000000 : ℝ)*x 1 + (3737659403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4189803083/10000000000 : ℝ)^4827 ≤ (16574294413497/50000000000000 : ℝ)^3803 := by
    have hnat : (4189803083 : ℕ)^4827*50000000000000^3803 ≤ 16574294413497^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4189803083 10000000000 16574294413497 50000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2341395671/5000000000 : ℝ)^4827 ≤ (4771935648039/12500000000000 : ℝ)^3803 := by
    have hnat : (2341395671 : ℕ)^4827*12500000000000^3803 ≤ 4771935648039^3803*5000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2341395671 5000000000 4771935648039 12500000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3737659403/10000000000 : ℝ)^4827 ≤ (28675925981091/100000000000000 : ℝ)^3803 := by
    have hnat : (3737659403 : ℕ)^4827*100000000000000^3803 ≤ 28675925981091^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3737659403 10000000000 28675925981091 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4189803083/10000000000 : ℝ), (2341395671/5000000000 : ℝ), (3737659403/10000000000 : ℝ)] ![(16574294413497/50000000000000 : ℝ), (4771935648039/12500000000000 : ℝ), (28675925981091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4189803083/10000000000 : ℝ)|^4827 ≤ (16574294413497/50000000000000 : ℝ)^3803
        have hw : |(4189803083/10000000000 : ℝ)|=(4189803083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2341395671/5000000000 : ℝ)|^4827 ≤ (4771935648039/12500000000000 : ℝ)^3803
        have hw : |(2341395671/5000000000 : ℝ)|=(2341395671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3737659403/10000000000 : ℝ)|^4827 ≤ (28675925981091/100000000000000 : ℝ)^3803
        have hw : |(3737659403/10000000000 : ℝ)|=(3737659403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1627_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175621841/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23857/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4383/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4709/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4393/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (23857/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4383/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (23857/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4383/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (23857/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4383/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (23857/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4383/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (23857/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4383/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (23857/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4383/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4383/100000 : ℝ) ^ (4823/1024 : ℝ) ≤ (8013581870567/20000000000000000000 : ℝ) := by
    have hpowers : (4383/100000 : ℝ)^4823 ≤ (8013581870567/20000000000000000000 : ℝ)^1024 := by
      have hnat : (4383 : ℕ)^4823*20000000000000000000^1024 ≤ 8013581870567^1024*100000^4823 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4383 100000 8013581870567 20000000000000000000 4823 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4383/100000 : ℝ)) (X := (8013581870567/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4823 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (23857/100000 : ℝ) ^ (4823/1024 : ℝ) ≤ (117110240760091999/100000000000000000000 : ℝ) := by
    have hpowers : (23857/100000 : ℝ)^4823 ≤ (117110240760091999/100000000000000000000 : ℝ)^1024 := by
      have hnat : (23857 : ℕ)^4823*100000000000000000000^1024 ≤ 117110240760091999^1024*100000^4823 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23857 100000 117110240760091999 100000000000000000000 4823 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (23857/100000 : ℝ)) (X := (117110240760091999/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4823 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000008013581870567/10000000000000000000 : ℝ) ≤ (10000001701410999/10000000000000000 : ℝ) ^ (4823/1024 : ℝ) := by
    have hpowers : (10000008013581870567/10000000000000000000 : ℝ)^1024 ≤ (10000001701410999/10000000000000000 : ℝ)^4823 := by
      have hnat : (10000008013581870567 : ℕ)^1024*10000000000000000^4823 ≤ 10000001701410999^4823*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000008013581870567 10000000000000000000 10000001701410999 10000000000000000 1024 4823 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001701410999/10000000000000000 : ℝ)) (X := (10000008013581870567/10000000000000000000 : ℝ)) (by norm_num) 4823 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50058575154334722417/50000000000000000000 : ℝ) ≤ (10002486141526039/10000000000000000 : ℝ) ^ (4823/1024 : ℝ) := by
    have hpowers : (50058575154334722417/50000000000000000000 : ℝ)^1024 ≤ (10002486141526039/10000000000000000 : ℝ)^4823 := by
      have hnat : (50058575154334722417 : ℕ)^1024*10000000000000000^4823 ≤ 10002486141526039^4823*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50058575154334722417 50000000000000000000 10002486141526039 10000000000000000 1024 4823 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002486141526039/10000000000000000 : ℝ)) (X := (50058575154334722417/50000000000000000000 : ℝ)) (by norm_num) 4823 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50117110240760091999/50000000000000000000 : ℝ) ≤ (10004970581641079/10000000000000000 : ℝ) ^ (4823/1024 : ℝ) := by
    have hpowers : (50117110240760091999/50000000000000000000 : ℝ)^1024 ≤ (10004970581641079/10000000000000000 : ℝ)^4823 := by
      have hnat : (50117110240760091999 : ℕ)^1024*10000000000000000^4823 ≤ 10004970581641079^4823*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50117110240760091999 50000000000000000000 10004970581641079 10000000000000000 1024 4823 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004970581641079/10000000000000000 : ℝ)) (X := (50117110240760091999/50000000000000000000 : ℝ)) (by norm_num) 4823 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8013581870567/20000000000000000000 : ℝ) ≤ ((7489163635816513611/7490000000000000000 : ℝ)+2*(1194442363/936250000000 : ℝ)*(4383/100000 : ℝ))^(4823/1024 : ℝ) := by
    rw [show (7489163635816513611/7490000000000000000 : ℝ)+2*(1194442363/936250000000 : ℝ)*(4383/100000 : ℝ)=(10000001701410999/10000000000000000 : ℝ) by norm_num, show 1+2*(8013581870567/20000000000000000000 : ℝ)=(10000008013581870567/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(117110240760091999/100000000000000000000 : ℝ)+(8013581870567/20000000000000000000 : ℝ) ≤ ((7489163635816513611/7490000000000000000 : ℝ)+(1194442363/936250000000 : ℝ)*((23857/100000 : ℝ)+(4383/100000 : ℝ)))^(4823/1024 : ℝ) := by
    rw [show (7489163635816513611/7490000000000000000 : ℝ)+(1194442363/936250000000 : ℝ)*((23857/100000 : ℝ)+(4383/100000 : ℝ))=(10002486141526039/10000000000000000 : ℝ) by norm_num, show 1+(117110240760091999/100000000000000000000 : ℝ)+(8013581870567/20000000000000000000 : ℝ)=(50058575154334722417/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(117110240760091999/100000000000000000000 : ℝ) ≤ ((7489163635816513611/7490000000000000000 : ℝ)+2*(1194442363/936250000000 : ℝ)*(23857/100000 : ℝ))^(4823/1024 : ℝ) := by
    rw [show (7489163635816513611/7490000000000000000 : ℝ)+2*(1194442363/936250000000 : ℝ)*(23857/100000 : ℝ)=(10004970581641079/10000000000000000 : ℝ) by norm_num, show 1+2*(117110240760091999/100000000000000000000 : ℝ)=(50117110240760091999/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7489163635816513611/7490000000000000000 : ℝ)*(X 1 0+X 2 0)+(1194442363/936250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4823/1024 : ℝ)) (lo := (4383/100000 : ℝ)) (hi := (23857/100000 : ℝ)) (c := (7489163635816513611/7490000000000000000 : ℝ)) (alpha := (1194442363/936250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7489163635816513611/7490000000000000000 : ℝ)*(X 0 1+X 2 1)+(1194442363/936250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4823/1024 : ℝ)) (lo := (4383/100000 : ℝ)) (hi := (23857/100000 : ℝ)) (c := (7489163635816513611/7490000000000000000 : ℝ)) (alpha := (1194442363/936250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7489163635816513611/7490000000000000000 : ℝ)*(X 0 2+X 1 2)+(1194442363/936250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4823/1024 : ℝ)) (lo := (4383/100000 : ℝ)) (hi := (23857/100000 : ℝ)) (c := (7489163635816513611/7490000000000000000 : ℝ)) (alpha := (1194442363/936250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-824799563/5000000000 : ℝ)*X 0 0+(5514687331/10000000000 : ℝ)*X 0 1+(1026067973/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1073400777/2000000000 : ℝ)*X 1 0+(-925030917/5000000000 : ℝ)*X 1 1+(2565169821/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5367004449/10000000000 : ℝ)*X 2 0+(1282584731/2500000000 : ℝ)*X 2 1+(-462515507/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((418932613/1000000000 : ℝ)*X 0 0+(186366197/500000000 : ℝ)*X 0 1+(4692974363/10000000000 : ℝ)*X 0 2+(418932613/1000000000 : ℝ)*X 1 0+(186366197/500000000 : ℝ)*X 1 1+(4692974363/10000000000 : ℝ)*X 1 2+(418932613/1000000000 : ℝ)*X 2 0+(186366197/500000000 : ℝ)*X 2 1+(4692974363/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-329957999/2000000000 : ℝ)*X 0 0+(1026878651/2000000000 : ℝ)*X 0 1+(1377643319/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2632256443/5000000000 : ℝ)*X 1 0+(-1469827443/10000000000 : ℝ)*X 1 1+(5510573619/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1052902447/2000000000 : ℝ)*X 2 0+(2755286929/5000000000 : ℝ)*X 2 1+(-1469828019/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4189803083/10000000000 : ℝ)*X 0 0+(2341395671/5000000000 : ℝ)*X 0 1+(3737659403/10000000000 : ℝ)*X 0 2+(4189803083/10000000000 : ℝ)*X 1 0+(2341395671/5000000000 : ℝ)*X 1 1+(3737659403/10000000000 : ℝ)*X 1 2+(4189803083/10000000000 : ℝ)*X 2 0+(2341395671/5000000000 : ℝ)*X 2 1+(3737659403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3689748184860166478704265217/374500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26101857/6250000000000 : ℝ)*(base1) + (318628119/20000000000000 : ℝ)*(base19) + (186655749/10000000000000 : ℝ)*(base23) + (348257/160000000000 : ℝ)*(upper3) + (18415253/12500000000000 : ℝ)*(upper5) + (1818703466706849/100000000000000 : ℝ)*(major0) + (1818703466706849/100000000000000 : ℝ)*(major1) + (1818703466706849/100000000000000 : ℝ)*(major2) + (2540840023941/97656250000 : ℝ)*(sp0) + (1300912845955111/50000000000000 : ℝ)*(sp1) + (162614088655833/6250000000000 : ℝ)*(sp2) + (517787381445627/50000000000000 : ℝ)*(sp3) + (469885309/6250000000000 : ℝ)*(sp4) + (1034856601/25000000000000 : ℝ)*(sp7) + (1035579319947369/100000000000000 : ℝ)*(f.failure) + (2601827285050817/100000000000000 : ℝ)*(f.sum) + (49792762583/18725000000000000000000000 : ℝ)*base66 + (5949326066003421739/749000000000000000000000000000000 : ℝ)*base67 + (5693949448269421739/749000000000000000000000000000000 : ℝ)*base69 + (1250847687426578261/749000000000000000000000000000000 : ℝ)*base72 + (760244054943/187250000000000000000000000 : ℝ)*base73 + (1313865188910578261/749000000000000000000000000000000 : ℝ)*base76 + (4027842935124578261/749000000000000000000000000000000 : ℝ)*base78 + (7656094189948578261/749000000000000000000000000000000 : ℝ)*base80 + (1617745366661/374500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base87 + (66886329/10000000000000000000000 : ℝ)*base89 + (66886329/10000000000000000000000 : ℝ)*base91 + (66886329/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3395373174835171975539/374500000000000000000000000 : ℝ) := by norm_num
    linear_combination (447667851/25000000000000 : ℝ)*(base19) + (1510131113/100000000000000 : ℝ)*(base23) + (30789797/100000000000000 : ℝ)*(upper2) + (375573189/100000000000000 : ℝ)*(upper3) + (81597107/100000000000000 : ℝ)*(upper5) + (464543742720727/25000000000000 : ℝ)*(major0) + (464543742720727/25000000000000 : ℝ)*(major1) + (464543742720727/25000000000000 : ℝ)*(major2) + (3415759153/25000000000000 : ℝ)*(sp1) + (3283374811/25000000000000 : ℝ)*(sp2) + (1329147518757369/50000000000000 : ℝ)*(sp4) + (1329139791903361/50000000000000 : ℝ)*(sp5) + (2658280393884381/100000000000000 : ℝ)*(sp6) + (529027301018587/50000000000000 : ℝ)*(sp7) + (529027301018587/50000000000000 : ℝ)*(f.failure) + (1329147518757369/50000000000000 : ℝ)*(f.sum) + (1095434295551/187250000000000000000000000 : ℝ)*base66 + (123264580524815197/187250000000000000000000000000000 : ℝ)*base67 + (152054434302815197/187250000000000000000000000000000 : ℝ)*base69 + (80842611211184803/187250000000000000000000000000000 : ℝ)*base72 + (1393800812791/374500000000000000000000000 : ℝ)*base74 + (187613558711315197/187250000000000000000000000000000 : ℝ)*base75 + (835905912078934803/187250000000000000000000000000000 : ℝ)*base78 + (1764326489434184803/187250000000000000000000000000000 : ℝ)*base80 + (207776242707/149800000000000000000000000 : ℝ)*base82 + (24158667/5000000000000000000000 : ℝ)*base89 + (24158667/5000000000000000000000 : ℝ)*base91 + (24158667/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1627_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175621841/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23857/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4383/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4709/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4393/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1627_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1627_s2_0 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-207666989/1250000000 : ℝ)*x 0 + (5459714543/10000000000 : ℝ)*x 1 + (647200411/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (207666989/1250000000 : ℝ)^4827 ≤ (10246061582447/100000000000000 : ℝ)^3803 := by
    have hnat : (207666989 : ℕ)^4827*100000000000000^3803 ≤ 10246061582447^3803*1250000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207666989 1250000000 10246061582447 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5459714543/10000000000 : ℝ)^4827 ≤ (23193699513131/50000000000000 : ℝ)^3803 := by
    have hnat : (5459714543 : ℕ)^4827*50000000000000^3803 ≤ 23193699513131^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459714543 10000000000 23193699513131 50000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (647200411/1250000000 : ℝ)^4827 ≤ (43366539382903/100000000000000 : ℝ)^3803 := by
    have hnat : (647200411 : ℕ)^4827*100000000000000^3803 ≤ 43366539382903^3803*1250000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647200411 1250000000 43366539382903 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-207666989/1250000000 : ℝ), (5459714543/10000000000 : ℝ), (647200411/1250000000 : ℝ)] ![(10246061582447/100000000000000 : ℝ), (23193699513131/50000000000000 : ℝ), (43366539382903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-207666989/1250000000 : ℝ)|^4827 ≤ (10246061582447/100000000000000 : ℝ)^3803
        have hw : |(-207666989/1250000000 : ℝ)|=(207666989/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5459714543/10000000000 : ℝ)|^4827 ≤ (23193699513131/50000000000000 : ℝ)^3803
        have hw : |(5459714543/10000000000 : ℝ)|=(5459714543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(647200411/1250000000 : ℝ)|^4827 ≤ (43366539382903/100000000000000 : ℝ)^3803
        have hw : |(647200411/1250000000 : ℝ)|=(647200411/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s2_1 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352576977/10000000000 : ℝ)*x 0 + (-903429229/5000000000 : ℝ)*x 1 + (517760333/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352576977/10000000000 : ℝ)^4827 ≤ (9047018293841/20000000000000 : ℝ)^3803 := by
    have hnat : (5352576977 : ℕ)^4827*20000000000000^3803 ≤ 9047018293841^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352576977 10000000000 9047018293841 20000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (903429229/5000000000 : ℝ)^4827 ≤ (5699184345339/50000000000000 : ℝ)^3803 := by
    have hnat : (903429229 : ℕ)^4827*50000000000000^3803 ≤ 5699184345339^3803*5000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903429229 5000000000 5699184345339 50000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (517760333/1000000000 : ℝ)^4827 ≤ (1355204369669/3125000000000 : ℝ)^3803 := by
    have hnat : (517760333 : ℕ)^4827*3125000000000^3803 ≤ 1355204369669^3803*1000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517760333 1000000000 1355204369669 3125000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352576977/10000000000 : ℝ), (-903429229/5000000000 : ℝ), (517760333/1000000000 : ℝ)] ![(9047018293841/20000000000000 : ℝ), (5699184345339/50000000000000 : ℝ), (1355204369669/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352576977/10000000000 : ℝ)|^4827 ≤ (9047018293841/20000000000000 : ℝ)^3803
        have hw : |(5352576977/10000000000 : ℝ)|=(5352576977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-903429229/5000000000 : ℝ)|^4827 ≤ (5699184345339/50000000000000 : ℝ)^3803
        have hw : |(-903429229/5000000000 : ℝ)|=(903429229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(517760333/1000000000 : ℝ)|^4827 ≤ (1355204369669/3125000000000 : ℝ)^3803
        have hw : |(517760333/1000000000 : ℝ)|=(517760333/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s2_2 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676288517/5000000000 : ℝ)*x 0 + (5177603231/10000000000 : ℝ)*x 1 + (-1806858513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676288517/5000000000 : ℝ)^4827 ≤ (45235092080623/100000000000000 : ℝ)^3803 := by
    have hnat : (2676288517 : ℕ)^4827*100000000000000^3803 ≤ 45235092080623^3803*5000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676288517 5000000000 45235092080623 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5177603231/10000000000 : ℝ)^4827 ≤ (10841634694233/25000000000000 : ℝ)^3803 := by
    have hnat : (5177603231 : ℕ)^4827*25000000000000^3803 ≤ 10841634694233^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177603231 10000000000 10841634694233 25000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1806858513/10000000000 : ℝ)^4827 ≤ (11398369131063/100000000000000 : ℝ)^3803 := by
    have hnat : (1806858513 : ℕ)^4827*100000000000000^3803 ≤ 11398369131063^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1806858513 10000000000 11398369131063 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676288517/5000000000 : ℝ), (5177603231/10000000000 : ℝ), (-1806858513/10000000000 : ℝ)] ![(45235092080623/100000000000000 : ℝ), (10841634694233/25000000000000 : ℝ), (11398369131063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676288517/5000000000 : ℝ)|^4827 ≤ (45235092080623/100000000000000 : ℝ)^3803
        have hw : |(2676288517/5000000000 : ℝ)|=(2676288517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5177603231/10000000000 : ℝ)|^4827 ≤ (10841634694233/25000000000000 : ℝ)^3803
        have hw : |(5177603231/10000000000 : ℝ)|=(5177603231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1806858513/10000000000 : ℝ)|^4827 ≤ (11398369131063/100000000000000 : ℝ)^3803
        have hw : |(-1806858513/10000000000 : ℝ)|=(1806858513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s2_3 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4198026051/10000000000 : ℝ)*x 0 + (240928473/625000000 : ℝ)*x 1 + (4563642251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4198026051/10000000000 : ℝ)^4827 ≤ (6646237219239/20000000000000 : ℝ)^3803 := by
    have hnat : (4198026051 : ℕ)^4827*20000000000000^3803 ≤ 6646237219239^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4198026051 10000000000 6646237219239 20000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (240928473/625000000 : ℝ)^4827 ≤ (14910980408457/50000000000000 : ℝ)^3803 := by
    have hnat : (240928473 : ℕ)^4827*50000000000000^3803 ≤ 14910980408457^3803*625000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240928473 625000000 14910980408457 50000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4563642251/10000000000 : ℝ)^4827 ≤ (3694685307421/10000000000000 : ℝ)^3803 := by
    have hnat : (4563642251 : ℕ)^4827*10000000000000^3803 ≤ 3694685307421^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4563642251 10000000000 3694685307421 10000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4198026051/10000000000 : ℝ), (240928473/625000000 : ℝ), (4563642251/10000000000 : ℝ)] ![(6646237219239/20000000000000 : ℝ), (14910980408457/50000000000000 : ℝ), (3694685307421/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4198026051/10000000000 : ℝ)|^4827 ≤ (6646237219239/20000000000000 : ℝ)^3803
        have hw : |(4198026051/10000000000 : ℝ)|=(4198026051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(240928473/625000000 : ℝ)|^4827 ≤ (14910980408457/50000000000000 : ℝ)^3803
        have hw : |(240928473/625000000 : ℝ)|=(240928473/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4563642251/10000000000 : ℝ)|^4827 ≤ (3694685307421/10000000000000 : ℝ)^3803
        have hw : |(4563642251/10000000000 : ℝ)|=(4563642251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s2_4 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-415352733/2500000000 : ℝ)*x 0 + (1294948521/2500000000 : ℝ)*x 1 + (5457500119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (415352733/2500000000 : ℝ)^4827 ≤ (81973190737/800000000000 : ℝ)^3803 := by
    have hnat : (415352733 : ℕ)^4827*800000000000^3803 ≤ 81973190737^3803*2500000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415352733 2500000000 81973190737 800000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1294948521/2500000000 : ℝ)^4827 ≤ (10847457803677/25000000000000 : ℝ)^3803 := by
    have hnat : (1294948521 : ℕ)^4827*25000000000000^3803 ≤ 10847457803677^3803*2500000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294948521 2500000000 10847457803677 25000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5457500119/10000000000 : ℝ)^4827 ≤ (2897719994819/6250000000000 : ℝ)^3803 := by
    have hnat : (5457500119 : ℕ)^4827*6250000000000^3803 ≤ 2897719994819^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457500119 10000000000 2897719994819 6250000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-415352733/2500000000 : ℝ), (1294948521/2500000000 : ℝ), (5457500119/10000000000 : ℝ)] ![(81973190737/800000000000 : ℝ), (10847457803677/25000000000000 : ℝ), (2897719994819/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-415352733/2500000000 : ℝ)|^4827 ≤ (81973190737/800000000000 : ℝ)^3803
        have hw : |(-415352733/2500000000 : ℝ)|=(415352733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1294948521/2500000000 : ℝ)|^4827 ≤ (10847457803677/25000000000000 : ℝ)^3803
        have hw : |(1294948521/2500000000 : ℝ)|=(1294948521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5457500119/10000000000 : ℝ)|^4827 ≤ (2897719994819/6250000000000 : ℝ)^3803
        have hw : |(5457500119/10000000000 : ℝ)|=(5457500119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s2_5 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277436021/10000000000 : ℝ)*x 0 + (-381740387/2500000000 : ℝ)*x 1 + (5457500261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277436021/10000000000 : ℝ)^4827 ≤ (11107652601091/25000000000000 : ℝ)^3803 := by
    have hnat : (5277436021 : ℕ)^4827*25000000000000^3803 ≤ 11107652601091^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277436021 10000000000 11107652601091 25000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (381740387/2500000000 : ℝ)^4827 ≤ (9205868129973/100000000000000 : ℝ)^3803 := by
    have hnat : (381740387 : ℕ)^4827*100000000000000^3803 ≤ 9205868129973^3803*2500000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      381740387 2500000000 9205868129973 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5457500261/10000000000 : ℝ)^4827 ≤ (46363521448269/100000000000000 : ℝ)^3803 := by
    have hnat : (5457500261 : ℕ)^4827*100000000000000^3803 ≤ 46363521448269^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457500261 10000000000 46363521448269 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277436021/10000000000 : ℝ), (-381740387/2500000000 : ℝ), (5457500261/10000000000 : ℝ)] ![(11107652601091/25000000000000 : ℝ), (9205868129973/100000000000000 : ℝ), (46363521448269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277436021/10000000000 : ℝ)|^4827 ≤ (11107652601091/25000000000000 : ℝ)^3803
        have hw : |(5277436021/10000000000 : ℝ)|=(5277436021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-381740387/2500000000 : ℝ)|^4827 ≤ (9205868129973/100000000000000 : ℝ)^3803
        have hw : |(-381740387/2500000000 : ℝ)|=(381740387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5457500261/10000000000 : ℝ)|^4827 ≤ (46363521448269/100000000000000 : ℝ)^3803
        have hw : |(5457500261/10000000000 : ℝ)|=(5457500261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s2_6 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638718533/5000000000 : ℝ)*x 0 + (5457498979/10000000000 : ℝ)*x 1 + (-305392379/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638718533/5000000000 : ℝ)^4827 ≤ (44430621571109/100000000000000 : ℝ)^3803 := by
    have hnat : (2638718533 : ℕ)^4827*100000000000000^3803 ≤ 44430621571109^3803*5000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638718533 5000000000 44430621571109 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5457498979/10000000000 : ℝ)^4827 ≤ (23181753812327/50000000000000 : ℝ)^3803 := by
    have hnat : (5457498979 : ℕ)^4827*50000000000000^3803 ≤ 23181753812327^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457498979 10000000000 23181753812327 50000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (305392379/2000000000 : ℝ)^4827 ≤ (1841174157059/20000000000000 : ℝ)^3803 := by
    have hnat : (305392379 : ℕ)^4827*20000000000000^3803 ≤ 1841174157059^3803*2000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      305392379 2000000000 1841174157059 20000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638718533/5000000000 : ℝ), (5457498979/10000000000 : ℝ), (-305392379/2000000000 : ℝ)] ![(44430621571109/100000000000000 : ℝ), (23181753812327/50000000000000 : ℝ), (1841174157059/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638718533/5000000000 : ℝ)|^4827 ≤ (44430621571109/100000000000000 : ℝ)^3803
        have hw : |(2638718533/5000000000 : ℝ)|=(2638718533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5457498979/10000000000 : ℝ)|^4827 ≤ (23181753812327/50000000000000 : ℝ)^3803
        have hw : |(5457498979/10000000000 : ℝ)|=(5457498979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-305392379/2000000000 : ℝ)|^4827 ≤ (1841174157059/20000000000000 : ℝ)^3803
        have hw : |(-305392379/2000000000 : ℝ)|=(305392379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s2_7 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4198215189/10000000000 : ℝ)*x 0 + (2279069909/5000000000 : ℝ)*x 1 + (3860418297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4198215189/10000000000 : ℝ)^4827 ≤ (16616543222043/50000000000000 : ℝ)^3803 := by
    have hnat : (4198215189 : ℕ)^4827*50000000000000^3803 ≤ 16616543222043^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4198215189 10000000000 16616543222043 50000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2279069909/5000000000 : ℝ)^4827 ≤ (36890320198943/100000000000000 : ℝ)^3803 := by
    have hnat : (2279069909 : ℕ)^4827*100000000000000^3803 ≤ 36890320198943^3803*5000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2279069909 5000000000 36890320198943 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3860418297/10000000000 : ℝ)^4827 ≤ (29876593344889/100000000000000 : ℝ)^3803 := by
    have hnat : (3860418297 : ℕ)^4827*100000000000000^3803 ≤ 29876593344889^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3860418297 10000000000 29876593344889 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4198215189/10000000000 : ℝ), (2279069909/5000000000 : ℝ), (3860418297/10000000000 : ℝ)] ![(16616543222043/50000000000000 : ℝ), (36890320198943/100000000000000 : ℝ), (29876593344889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4198215189/10000000000 : ℝ)|^4827 ≤ (16616543222043/50000000000000 : ℝ)^3803
        have hw : |(4198215189/10000000000 : ℝ)|=(4198215189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2279069909/5000000000 : ℝ)|^4827 ≤ (36890320198943/100000000000000 : ℝ)^3803
        have hw : |(2279069909/5000000000 : ℝ)|=(2279069909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3860418297/10000000000 : ℝ)|^4827 ≤ (29876593344889/100000000000000 : ℝ)^3803
        have hw : |(3860418297/10000000000 : ℝ)|=(3860418297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1627_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175621841/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4393/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4709/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10439/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8213/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4393/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4709/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4393/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4709/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4393/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4709/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4393/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4709/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4393/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4709/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4393/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4709/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4709/50000 : ℝ) ^ (4823/1024 : ℝ) ≤ (1470230714410511/100000000000000000000 : ℝ) := by
    have hpowers : (4709/50000 : ℝ)^4823 ≤ (1470230714410511/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4709 : ℕ)^4823*100000000000000000000^1024 ≤ 1470230714410511^1024*50000^4823 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4709 50000 1470230714410511 100000000000000000000 4823 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4709/50000 : ℝ)) (X := (1470230714410511/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4823 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4393/25000 : ℝ) ^ (4823/1024 : ℝ) ≤ (27741971785675231/100000000000000000000 : ℝ) := by
    have hpowers : (4393/25000 : ℝ)^4823 ≤ (27741971785675231/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4393 : ℕ)^4823*100000000000000000000^1024 ≤ 27741971785675231^1024*25000^4823 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4393 25000 27741971785675231 100000000000000000000 4823 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4393/25000 : ℝ)) (X := (27741971785675231/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4823 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001470230714410511/50000000000000000000 : ℝ) ≤ (625003901873359/625000000000000 : ℝ) ^ (4823/1024 : ℝ) := by
    have hpowers : (50001470230714410511/50000000000000000000 : ℝ)^1024 ≤ (625003901873359/625000000000000 : ℝ)^4823 := by
      have hnat : (50001470230714410511 : ℕ)^1024*625000000000000^4823 ≤ 625003901873359^4823*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001470230714410511 50000000000000000000 625003901873359 625000000000000 1024 4823 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625003901873359/625000000000000 : ℝ)) (X := (50001470230714410511/50000000000000000000 : ℝ)) (by norm_num) 4823 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50014606101250042871/50000000000000000000 : ℝ) ≤ (10000620150413367/10000000000000000 : ℝ) ^ (4823/1024 : ℝ) := by
    have hpowers : (50014606101250042871/50000000000000000000 : ℝ)^1024 ≤ (10000620150413367/10000000000000000 : ℝ)^4823 := by
      have hnat : (50014606101250042871 : ℕ)^1024*10000000000000000^4823 ≤ 10000620150413367^4823*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014606101250042871 50000000000000000000 10000620150413367 10000000000000000 1024 4823 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000620150413367/10000000000000000 : ℝ)) (X := (50014606101250042871/50000000000000000000 : ℝ)) (by norm_num) 4823 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027741971785675231/50000000000000000000 : ℝ) ≤ (1000117787085299/1000000000000000 : ℝ) ^ (4823/1024 : ℝ) := by
    have hpowers : (50027741971785675231/50000000000000000000 : ℝ)^1024 ≤ (1000117787085299/1000000000000000 : ℝ)^4823 := by
      have hnat : (50027741971785675231 : ℕ)^1024*1000000000000000^4823 ≤ 1000117787085299^4823*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027741971785675231 50000000000000000000 1000117787085299 1000000000000000 1024 4823 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000117787085299/1000000000000000 : ℝ)) (X := (50027741971785675231/50000000000000000000 : ℝ)) (by norm_num) 4823 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1470230714410511/100000000000000000000 : ℝ) ≤ ((20382500957951292437/20385000000000000000 : ℝ)+2*(557720439623/815400000000000 : ℝ)*(4709/50000 : ℝ))^(4823/1024 : ℝ) := by
    rw [show (20382500957951292437/20385000000000000000 : ℝ)+2*(557720439623/815400000000000 : ℝ)*(4709/50000 : ℝ)=(625003901873359/625000000000000 : ℝ) by norm_num, show 1+2*(1470230714410511/100000000000000000000 : ℝ)=(50001470230714410511/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27741971785675231/100000000000000000000 : ℝ)+(1470230714410511/100000000000000000000 : ℝ) ≤ ((20382500957951292437/20385000000000000000 : ℝ)+(557720439623/815400000000000 : ℝ)*((4393/25000 : ℝ)+(4709/50000 : ℝ)))^(4823/1024 : ℝ) := by
    rw [show (20382500957951292437/20385000000000000000 : ℝ)+(557720439623/815400000000000 : ℝ)*((4393/25000 : ℝ)+(4709/50000 : ℝ))=(10000620150413367/10000000000000000 : ℝ) by norm_num, show 1+(27741971785675231/100000000000000000000 : ℝ)+(1470230714410511/100000000000000000000 : ℝ)=(50014606101250042871/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27741971785675231/100000000000000000000 : ℝ) ≤ ((20382500957951292437/20385000000000000000 : ℝ)+2*(557720439623/815400000000000 : ℝ)*(4393/25000 : ℝ))^(4823/1024 : ℝ) := by
    rw [show (20382500957951292437/20385000000000000000 : ℝ)+2*(557720439623/815400000000000 : ℝ)*(4393/25000 : ℝ)=(1000117787085299/1000000000000000 : ℝ) by norm_num, show 1+2*(27741971785675231/100000000000000000000 : ℝ)=(50027741971785675231/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (20382500957951292437/20385000000000000000 : ℝ)*(X 1 0+X 2 0)+(557720439623/815400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4823/1024 : ℝ)) (lo := (4709/50000 : ℝ)) (hi := (4393/25000 : ℝ)) (c := (20382500957951292437/20385000000000000000 : ℝ)) (alpha := (557720439623/815400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (20382500957951292437/20385000000000000000 : ℝ)*(X 0 1+X 2 1)+(557720439623/815400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4823/1024 : ℝ)) (lo := (4709/50000 : ℝ)) (hi := (4393/25000 : ℝ)) (c := (20382500957951292437/20385000000000000000 : ℝ)) (alpha := (557720439623/815400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (20382500957951292437/20385000000000000000 : ℝ)*(X 0 2+X 1 2)+(557720439623/815400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4823/1024 : ℝ)) (lo := (4709/50000 : ℝ)) (hi := (4393/25000 : ℝ)) (c := (20382500957951292437/20385000000000000000 : ℝ)) (alpha := (557720439623/815400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-207666989/1250000000 : ℝ)*X 0 0+(5459714543/10000000000 : ℝ)*X 0 1+(647200411/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352576977/10000000000 : ℝ)*X 1 0+(-903429229/5000000000 : ℝ)*X 1 1+(517760333/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676288517/5000000000 : ℝ)*X 2 0+(5177603231/10000000000 : ℝ)*X 2 1+(-1806858513/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4198026051/10000000000 : ℝ)*X 0 0+(240928473/625000000 : ℝ)*X 0 1+(4563642251/10000000000 : ℝ)*X 0 2+(4198026051/10000000000 : ℝ)*X 1 0+(240928473/625000000 : ℝ)*X 1 1+(4563642251/10000000000 : ℝ)*X 1 2+(4198026051/10000000000 : ℝ)*X 2 0+(240928473/625000000 : ℝ)*X 2 1+(4563642251/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-415352733/2500000000 : ℝ)*X 0 0+(1294948521/2500000000 : ℝ)*X 0 1+(5457500119/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5277436021/10000000000 : ℝ)*X 1 0+(-381740387/2500000000 : ℝ)*X 1 1+(5457500261/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2638718533/5000000000 : ℝ)*X 2 0+(5457498979/10000000000 : ℝ)*X 2 1+(-305392379/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4198215189/10000000000 : ℝ)*X 0 0+(2279069909/5000000000 : ℝ)*X 0 1+(3860418297/10000000000 : ℝ)*X 0 2+(4198215189/10000000000 : ℝ)*X 1 0+(2279069909/5000000000 : ℝ)*X 1 1+(3860418297/10000000000 : ℝ)*X 1 2+(4198215189/10000000000 : ℝ)*X 2 0+(2279069909/5000000000 : ℝ)*X 2 1+(3860418297/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (175638493909897970660061089/28312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (191003027/20000000000000 : ℝ)*(base19) + (229874687/25000000000000 : ℝ)*(base23) + (39215341/100000000000000 : ℝ)*(lower2) + (16980467/10000000000000 : ℝ)*(upper3) + (9936921/12500000000000 : ℝ)*(upper5) + (619449372417909/25000000000000 : ℝ)*(major0) + (619449372417909/25000000000000 : ℝ)*(major1) + (619449372417909/25000000000000 : ℝ)*(major2) + (1772356464939257/50000000000000 : ℝ)*(sp0) + (1772361447110323/50000000000000 : ℝ)*(sp1) + (1772361464868517/50000000000000 : ℝ)*(sp2) + (352716457136759/25000000000000 : ℝ)*(sp3) + (10919357267/100000000000000 : ℝ)*(sp4) + (5094774873/100000000000000 : ℝ)*(sp7) + (1410870923321909/100000000000000 : ℝ)*(f.failure) + (3544723849235781/100000000000000 : ℝ)*(f.sum) + (6690222418843/6795000000000000000000000000 : ℝ)*base65 + (1776705227394076411/169875000000000000000000000000000 : ℝ)*base67 + (1620537266172826411/169875000000000000000000000000000 : ℝ)*base69 + (954659567394451411/169875000000000000000000000000000 : ℝ)*base71 + (2670738839351/849375000000000000000000000 : ℝ)*base73 + (571085064780298589/169875000000000000000000000000000 : ℝ)*base76 + (1343671616266201411/169875000000000000000000000000000 : ℝ)*base77 + (1352514467770423589/169875000000000000000000000000000 : ℝ)*base80 + (23928759249913/6795000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (105785531/10000000000000000000000 : ℝ)*base90 + (105785531/10000000000000000000000 : ℝ)*base92 + (105785531/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (452728686989176867711693391/67950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (669565731/100000000000000 : ℝ)*(base19) + (830108177/50000000000000 : ℝ)*(base23) + (95762011/100000000000000 : ℝ)*(upper3) + (67831293/50000000000000 : ℝ)*(lower4) + (503417015820719/20000000000000 : ℝ)*(major0) + (503417015820719/20000000000000 : ℝ)*(major1) + (503417015820719/20000000000000 : ℝ)*(major2) + (927203407/10000000000000 : ℝ)*(sp1) + (669758767/6250000000000 : ℝ)*(sp2) + (1856487091/100000000000000 : ℝ)*(sp3) + (180046422636449/5000000000000 : ℝ)*(sp4) + (3600918511129179/100000000000000 : ℝ)*(sp5) + (720183215274471/20000000000000 : ℝ)*(sp6) + (1433239626901979/100000000000000 : ℝ)*(sp7) + (143324148338907/10000000000000 : ℝ)*(f.failure) + (180046422636449/5000000000000 : ℝ)*(f.sum) + (39585640026889/8154000000000000000000000000 : ℝ)*base65 + (3192155652465027203/407700000000000000000000000000000 : ℝ)*base67 + (5171207531731227203/407700000000000000000000000000000 : ℝ)*base69 + (6600118733034327203/407700000000000000000000000000000 : ℝ)*base71 + (1014669083239/1630800000000000000000000000 : ℝ)*base74 + (1796299466598927203/407700000000000000000000000000000 : ℝ)*base75 + (711275255361027203/407700000000000000000000000000000 : ℝ)*base77 + (1017732526226127203/407700000000000000000000000000000 : ℝ)*base79 + (12501166506023/1630800000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (10732213/1000000000000000000000 : ℝ)*base90 + (10732213/1000000000000000000000 : ℝ)*base92 + (10732213/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1627_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175621841/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4393/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4709/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10439/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8213/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1627_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1627_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175621841/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10439/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8213/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1627_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1627_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1627_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175621841/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10439/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8213/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1627_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1349_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:07:19.909127+00:00
-- url     : https://prove2.me/submissions/c4e52e37-cb2b-49ce-885d-798aae4a264b

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
theorem support_rectangle_w1349_s6_0 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-407587129/2000000000 : ℝ)*x 0 + (676544651/1250000000 : ℝ)*x 1 + (1311202889/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (407587129/2000000000 : ℝ)^4309 ≤ (6206137077729/50000000000000 : ℝ)^3285 := by
    have hnat : (407587129 : ℕ)^4309*50000000000000^3285 ≤ 6206137077729^3285*2000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407587129 2000000000 6206137077729 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676544651/1250000000 : ℝ)^4309 ≤ (22348464893561/50000000000000 : ℝ)^3285 := by
    have hnat : (676544651 : ℕ)^4309*50000000000000^3285 ≤ 22348464893561^3285*1250000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676544651 1250000000 22348464893561 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311202889/2500000000 : ℝ)^4309 ≤ (4289079604887/10000000000000 : ℝ)^3285 := by
    have hnat : (1311202889 : ℕ)^4309*10000000000000^3285 ≤ 4289079604887^3285*2500000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311202889 2500000000 4289079604887 10000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-407587129/2000000000 : ℝ), (676544651/1250000000 : ℝ), (1311202889/2500000000 : ℝ)] ![(6206137077729/50000000000000 : ℝ), (22348464893561/50000000000000 : ℝ), (4289079604887/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-407587129/2000000000 : ℝ)|^4309 ≤ (6206137077729/50000000000000 : ℝ)^3285
        have hw : |(-407587129/2000000000 : ℝ)|=(407587129/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676544651/1250000000 : ℝ)|^4309 ≤ (22348464893561/50000000000000 : ℝ)^3285
        have hw : |(676544651/1250000000 : ℝ)|=(676544651/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311202889/2500000000 : ℝ)|^4309 ≤ (4289079604887/10000000000000 : ℝ)^3285
        have hw : |(1311202889/2500000000 : ℝ)|=(1311202889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s6_1 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674439703/5000000000 : ℝ)*x 0 + (-1061647981/5000000000 : ℝ)*x 1 + (1048962313/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674439703/5000000000 : ℝ)^4309 ≤ (35208448851/80000000000 : ℝ)^3285 := by
    have hnat : (2674439703 : ℕ)^4309*80000000000^3285 ≤ 35208448851^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674439703 5000000000 35208448851 80000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061647981/5000000000 : ℝ)^4309 ≤ (2619728555883/20000000000000 : ℝ)^3285 := by
    have hnat : (1061647981 : ℕ)^4309*20000000000000^3285 ≤ 2619728555883^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061647981 5000000000 2619728555883 20000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048962313/2000000000 : ℝ)^4309 ≤ (42890796145413/100000000000000 : ℝ)^3285 := by
    have hnat : (1048962313 : ℕ)^4309*100000000000000^3285 ≤ 42890796145413^3285*2000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048962313 2000000000 42890796145413 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674439703/5000000000 : ℝ), (-1061647981/5000000000 : ℝ), (1048962313/2000000000 : ℝ)] ![(35208448851/80000000000 : ℝ), (2619728555883/20000000000000 : ℝ), (42890796145413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674439703/5000000000 : ℝ)|^4309 ≤ (35208448851/80000000000 : ℝ)^3285
        have hw : |(2674439703/5000000000 : ℝ)|=(2674439703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1061647981/5000000000 : ℝ)|^4309 ≤ (2619728555883/20000000000000 : ℝ)^3285
        have hw : |(-1061647981/5000000000 : ℝ)|=(1061647981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048962313/2000000000 : ℝ)|^4309 ≤ (42890796145413/100000000000000 : ℝ)^3285
        have hw : |(1048962313/2000000000 : ℝ)|=(1048962313/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s6_2 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348879399/10000000000 : ℝ)*x 0 + (2622405779/5000000000 : ℝ)*x 1 + (-106164799/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348879399/10000000000 : ℝ)^4309 ≤ (220052804941/500000000000 : ℝ)^3285 := by
    have hnat : (5348879399 : ℕ)^4309*500000000000^3285 ≤ 220052804941^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348879399 10000000000 220052804941 500000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622405779/5000000000 : ℝ)^4309 ≤ (10722699017581/25000000000000 : ℝ)^3285 := by
    have hnat : (2622405779 : ℕ)^4309*25000000000000^3285 ≤ 10722699017581^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622405779 5000000000 10722699017581 25000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (106164799/500000000 : ℝ)^4309 ≤ (818665182817/6250000000000 : ℝ)^3285 := by
    have hnat : (106164799 : ℕ)^4309*6250000000000^3285 ≤ 818665182817^3285*500000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106164799 500000000 818665182817 6250000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348879399/10000000000 : ℝ), (2622405779/5000000000 : ℝ), (-106164799/500000000 : ℝ)] ![(220052804941/500000000000 : ℝ), (10722699017581/25000000000000 : ℝ), (818665182817/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348879399/10000000000 : ℝ)|^4309 ≤ (220052804941/500000000000 : ℝ)^3285
        have hw : |(5348879399/10000000000 : ℝ)|=(5348879399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622405779/5000000000 : ℝ)|^4309 ≤ (10722699017581/25000000000000 : ℝ)^3285
        have hw : |(2622405779/5000000000 : ℝ)|=(2622405779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-106164799/500000000 : ℝ)|^4309 ≤ (818665182817/6250000000000 : ℝ)^3285
        have hw : |(-106164799/500000000 : ℝ)|=(106164799/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s6_3 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4324791019/10000000000 : ℝ)*x 0 + (1038048613/2500000000 : ℝ)*x 1 + (4504055471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4324791019/10000000000 : ℝ)^4309 ≤ (16651685593209/50000000000000 : ℝ)^3285 := by
    have hnat : (4324791019 : ℕ)^4309*50000000000000^3285 ≤ 16651685593209^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4324791019 10000000000 16651685593209 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1038048613/2500000000 : ℝ)^4309 ≤ (31570919194849/100000000000000 : ℝ)^3285 := by
    have hnat : (1038048613 : ℕ)^4309*100000000000000^3285 ≤ 31570919194849^3285*2500000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038048613 2500000000 31570919194849 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4504055471/10000000000 : ℝ)^4309 ≤ (8781427400683/25000000000000 : ℝ)^3285 := by
    have hnat : (4504055471 : ℕ)^4309*25000000000000^3285 ≤ 8781427400683^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504055471 10000000000 8781427400683 25000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4324791019/10000000000 : ℝ), (1038048613/2500000000 : ℝ), (4504055471/10000000000 : ℝ)] ![(16651685593209/50000000000000 : ℝ), (31570919194849/100000000000000 : ℝ), (8781427400683/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4324791019/10000000000 : ℝ)|^4309 ≤ (16651685593209/50000000000000 : ℝ)^3285
        have hw : |(4324791019/10000000000 : ℝ)|=(4324791019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1038048613/2500000000 : ℝ)|^4309 ≤ (31570919194849/100000000000000 : ℝ)^3285
        have hw : |(1038048613/2500000000 : ℝ)|=(1038048613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4504055471/10000000000 : ℝ)|^4309 ≤ (8781427400683/25000000000000 : ℝ)^3285
        have hw : |(4504055471/10000000000 : ℝ)|=(4504055471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s6_4 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-15921467/78125000 : ℝ)*x 0 + (2622705899/5000000000 : ℝ)*x 1 + (5411753853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (15921467/78125000 : ℝ)^4309 ≤ (1551546384031/12500000000000 : ℝ)^3285 := by
    have hnat : (15921467 : ℕ)^4309*12500000000000^3285 ≤ 1551546384031^3285*78125000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15921467 78125000 1551546384031 12500000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622705899/5000000000 : ℝ)^4309 ≤ (10724308729007/25000000000000 : ℝ)^3285 := by
    have hnat : (2622705899 : ℕ)^4309*25000000000000^3285 ≤ 10724308729007^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622705899 5000000000 10724308729007 25000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411753853/10000000000 : ℝ)^4309 ≤ (8938078800503/20000000000000 : ℝ)^3285 := by
    have hnat : (5411753853 : ℕ)^4309*20000000000000^3285 ≤ 8938078800503^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411753853 10000000000 8938078800503 20000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-15921467/78125000 : ℝ), (2622705899/5000000000 : ℝ), (5411753853/10000000000 : ℝ)] ![(1551546384031/12500000000000 : ℝ), (10724308729007/25000000000000 : ℝ), (8938078800503/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-15921467/78125000 : ℝ)|^4309 ≤ (1551546384031/12500000000000 : ℝ)^3285
        have hw : |(-15921467/78125000 : ℝ)|=(15921467/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622705899/5000000000 : ℝ)|^4309 ≤ (10724308729007/25000000000000 : ℝ)^3285
        have hw : |(2622705899/5000000000 : ℝ)|=(2622705899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411753853/10000000000 : ℝ)|^4309 ≤ (8938078800503/20000000000000 : ℝ)^3285
        have hw : |(5411753853/10000000000 : ℝ)|=(5411753853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s6_5 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652844381/5000000000 : ℝ)*x 0 + (-391270741/2000000000 : ℝ)*x 1 + (5411753859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652844381/5000000000 : ℝ)^4309 ≤ (43544999662137/100000000000000 : ℝ)^3285 := by
    have hnat : (2652844381 : ℕ)^4309*100000000000000^3285 ≤ 43544999662137^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652844381 5000000000 43544999662137 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (391270741/2000000000 : ℝ)^4309 ≤ (11764606259991/100000000000000 : ℝ)^3285 := by
    have hnat : (391270741 : ℕ)^4309*100000000000000^3285 ≤ 11764606259991^3285*2000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      391270741 2000000000 11764606259991 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411753859/10000000000 : ℝ)^4309 ≤ (11172598516877/25000000000000 : ℝ)^3285 := by
    have hnat : (5411753859 : ℕ)^4309*25000000000000^3285 ≤ 11172598516877^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411753859 10000000000 11172598516877 25000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652844381/5000000000 : ℝ), (-391270741/2000000000 : ℝ), (5411753859/10000000000 : ℝ)] ![(43544999662137/100000000000000 : ℝ), (11764606259991/100000000000000 : ℝ), (11172598516877/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652844381/5000000000 : ℝ)|^4309 ≤ (43544999662137/100000000000000 : ℝ)^3285
        have hw : |(2652844381/5000000000 : ℝ)|=(2652844381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-391270741/2000000000 : ℝ)|^4309 ≤ (11764606259991/100000000000000 : ℝ)^3285
        have hw : |(-391270741/2000000000 : ℝ)|=(391270741/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411753859/10000000000 : ℝ)|^4309 ≤ (11172598516877/25000000000000 : ℝ)^3285
        have hw : |(5411753859/10000000000 : ℝ)|=(5411753859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s6_6 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305688763/10000000000 : ℝ)*x 0 + (5411753853/10000000000 : ℝ)*x 1 + (-1956353711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305688763/10000000000 : ℝ)^4309 ≤ (43544999672903/100000000000000 : ℝ)^3285 := by
    have hnat : (5305688763 : ℕ)^4309*100000000000000^3285 ≤ 43544999672903^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305688763 10000000000 43544999672903 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411753853/10000000000 : ℝ)^4309 ≤ (8938078800503/20000000000000 : ℝ)^3285 := by
    have hnat : (5411753853 : ℕ)^4309*20000000000000^3285 ≤ 8938078800503^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411753853 10000000000 8938078800503 20000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1956353711/10000000000 : ℝ)^4309 ≤ (11764606307319/100000000000000 : ℝ)^3285 := by
    have hnat : (1956353711 : ℕ)^4309*100000000000000^3285 ≤ 11764606307319^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1956353711 10000000000 11764606307319 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305688763/10000000000 : ℝ), (5411753853/10000000000 : ℝ), (-1956353711/10000000000 : ℝ)] ![(43544999672903/100000000000000 : ℝ), (8938078800503/20000000000000 : ℝ), (11764606307319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305688763/10000000000 : ℝ)|^4309 ≤ (43544999672903/100000000000000 : ℝ)^3285
        have hw : |(5305688763/10000000000 : ℝ)|=(5305688763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411753853/10000000000 : ℝ)|^4309 ≤ (8938078800503/20000000000000 : ℝ)^3285
        have hw : |(5411753853/10000000000 : ℝ)|=(5411753853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1956353711/10000000000 : ℝ)|^4309 ≤ (11764606307319/100000000000000 : ℝ)^3285
        have hw : |(-1956353711/10000000000 : ℝ)|=(1956353711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s6_7 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4324816469/10000000000 : ℝ)*x 0 + (4502794857/10000000000 : ℝ)*x 1 + (4153461547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4324816469/10000000000 : ℝ)^4309 ≤ (33303628256997/100000000000000 : ℝ)^3285 := by
    have hnat : (4324816469 : ℕ)^4309*100000000000000^3285 ≤ 33303628256997^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4324816469 10000000000 33303628256997 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4502794857/10000000000 : ℝ)^4309 ≤ (17556407237099/50000000000000 : ℝ)^3285 := by
    have hnat : (4502794857 : ℕ)^4309*50000000000000^3285 ≤ 17556407237099^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502794857 10000000000 17556407237099 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4153461547/10000000000 : ℝ)^4309 ≤ (31583557257223/100000000000000 : ℝ)^3285 := by
    have hnat : (4153461547 : ℕ)^4309*100000000000000^3285 ≤ 31583557257223^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4153461547 10000000000 31583557257223 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4324816469/10000000000 : ℝ), (4502794857/10000000000 : ℝ), (4153461547/10000000000 : ℝ)] ![(33303628256997/100000000000000 : ℝ), (17556407237099/50000000000000 : ℝ), (31583557257223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4324816469/10000000000 : ℝ)|^4309 ≤ (33303628256997/100000000000000 : ℝ)^3285
        have hw : |(4324816469/10000000000 : ℝ)|=(4324816469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4502794857/10000000000 : ℝ)|^4309 ≤ (17556407237099/50000000000000 : ℝ)^3285
        have hw : |(4502794857/10000000000 : ℝ)|=(4502794857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4153461547/10000000000 : ℝ)|^4309 ≤ (31583557257223/100000000000000 : ℝ)^3285
        have hw : |(4153461547/10000000000 : ℝ)|=(4153461547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1349_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4843891/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14719/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5579/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2233/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1839/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14719/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5579/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14719/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5579/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14719/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5579/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14719/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5579/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14719/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5579/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14719/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5579/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5579/50000 : ℝ) ^ (1077/256 : ℝ) ≤ (61524211808457/625000000000000000 : ℝ) := by
    have hpowers : (5579/50000 : ℝ)^1077 ≤ (61524211808457/625000000000000000 : ℝ)^256 := by
      have hnat : (5579 : ℕ)^1077*625000000000000000^256 ≤ 61524211808457^256*50000^1077 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5579 50000 61524211808457 625000000000000000 1077 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5579/50000 : ℝ)) (X := (61524211808457/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14719/100000 : ℝ) ^ (1077/256 : ℝ) ≤ (3156734281115951/10000000000000000000 : ℝ) := by
    have hpowers : (14719/100000 : ℝ)^1077 ≤ (3156734281115951/10000000000000000000 : ℝ)^256 := by
      have hnat : (14719 : ℕ)^1077*10000000000000000000^256 ≤ 3156734281115951^256*100000^1077 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14719 100000 3156734281115951 10000000000000000000 1077 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14719/100000 : ℝ)) (X := (3156734281115951/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (312561524211808457/312500000000000000 : ℝ) ≤ (10000467937350803/10000000000000000 : ℝ) ^ (1077/256 : ℝ) := by
    have hpowers : (312561524211808457/312500000000000000 : ℝ)^256 ≤ (10000467937350803/10000000000000000 : ℝ)^1077 := by
      have hnat : (312561524211808457 : ℕ)^256*10000000000000000^1077 ≤ 10000467937350803^1077*312500000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        312561524211808457 312500000000000000 10000467937350803 10000000000000000 256 1077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000467937350803/10000000000000000 : ℝ)) (X := (312561524211808457/312500000000000000 : ℝ)) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004141121670051263/10000000000000000000 : ℝ) ≤ (10000984178141489/10000000000000000 : ℝ) ^ (1077/256 : ℝ) := by
    have hpowers : (10004141121670051263/10000000000000000000 : ℝ)^256 ≤ (10000984178141489/10000000000000000 : ℝ)^1077 := by
      have hnat : (10004141121670051263 : ℕ)^256*10000000000000000^1077 ≤ 10000984178141489^1077*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004141121670051263 10000000000000000000 10000984178141489 10000000000000000 256 1077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000984178141489/10000000000000000 : ℝ)) (X := (10004141121670051263/10000000000000000000 : ℝ)) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003156734281115951/5000000000000000000 : ℝ) ≤ (400060016757287/400000000000000 : ℝ) ^ (1077/256 : ℝ) := by
    have hpowers : (5003156734281115951/5000000000000000000 : ℝ)^256 ≤ (400060016757287/400000000000000 : ℝ)^1077 := by
      have hnat : (5003156734281115951 : ℕ)^256*400000000000000^1077 ≤ 400060016757287^1077*5000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003156734281115951 5000000000000000000 400060016757287 400000000000000 256 1077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400060016757287/400000000000000 : ℝ)) (X := (5003156734281115951/5000000000000000000 : ℝ)) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(61524211808457/625000000000000000 : ℝ) ≤ ((11866715298473753569/11870000000000000000 : ℝ)+2*(86040131781/59350000000000 : ℝ)*(5579/50000 : ℝ))^(1077/256 : ℝ) := by
    rw [show (11866715298473753569/11870000000000000000 : ℝ)+2*(86040131781/59350000000000 : ℝ)*(5579/50000 : ℝ)=(10000467937350803/10000000000000000 : ℝ) by norm_num, show 1+2*(61524211808457/625000000000000000 : ℝ)=(312561524211808457/312500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3156734281115951/10000000000000000000 : ℝ)+(61524211808457/625000000000000000 : ℝ) ≤ ((11866715298473753569/11870000000000000000 : ℝ)+(86040131781/59350000000000 : ℝ)*((14719/100000 : ℝ)+(5579/50000 : ℝ)))^(1077/256 : ℝ) := by
    rw [show (11866715298473753569/11870000000000000000 : ℝ)+(86040131781/59350000000000 : ℝ)*((14719/100000 : ℝ)+(5579/50000 : ℝ))=(10000984178141489/10000000000000000 : ℝ) by norm_num, show 1+(3156734281115951/10000000000000000000 : ℝ)+(61524211808457/625000000000000000 : ℝ)=(10004141121670051263/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3156734281115951/10000000000000000000 : ℝ) ≤ ((11866715298473753569/11870000000000000000 : ℝ)+2*(86040131781/59350000000000 : ℝ)*(14719/100000 : ℝ))^(1077/256 : ℝ) := by
    rw [show (11866715298473753569/11870000000000000000 : ℝ)+2*(86040131781/59350000000000 : ℝ)*(14719/100000 : ℝ)=(400060016757287/400000000000000 : ℝ) by norm_num, show 1+2*(3156734281115951/10000000000000000000 : ℝ)=(5003156734281115951/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11866715298473753569/11870000000000000000 : ℝ)*(X 1 0+X 2 0)+(86040131781/59350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1077/256 : ℝ)) (lo := (5579/50000 : ℝ)) (hi := (14719/100000 : ℝ)) (c := (11866715298473753569/11870000000000000000 : ℝ)) (alpha := (86040131781/59350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11866715298473753569/11870000000000000000 : ℝ)*(X 0 1+X 2 1)+(86040131781/59350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1077/256 : ℝ)) (lo := (5579/50000 : ℝ)) (hi := (14719/100000 : ℝ)) (c := (11866715298473753569/11870000000000000000 : ℝ)) (alpha := (86040131781/59350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11866715298473753569/11870000000000000000 : ℝ)*(X 0 2+X 1 2)+(86040131781/59350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1077/256 : ℝ)) (lo := (5579/50000 : ℝ)) (hi := (14719/100000 : ℝ)) (c := (11866715298473753569/11870000000000000000 : ℝ)) (alpha := (86040131781/59350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-407587129/2000000000 : ℝ)*X 0 0+(676544651/1250000000 : ℝ)*X 0 1+(1311202889/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674439703/5000000000 : ℝ)*X 1 0+(-1061647981/5000000000 : ℝ)*X 1 1+(1048962313/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348879399/10000000000 : ℝ)*X 2 0+(2622405779/5000000000 : ℝ)*X 2 1+(-106164799/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4324791019/10000000000 : ℝ)*X 0 0+(1038048613/2500000000 : ℝ)*X 0 1+(4504055471/10000000000 : ℝ)*X 0 2+(4324791019/10000000000 : ℝ)*X 1 0+(1038048613/2500000000 : ℝ)*X 1 1+(4504055471/10000000000 : ℝ)*X 1 2+(4324791019/10000000000 : ℝ)*X 2 0+(1038048613/2500000000 : ℝ)*X 2 1+(4504055471/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-15921467/78125000 : ℝ)*X 0 0+(2622705899/5000000000 : ℝ)*X 0 1+(5411753853/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652844381/5000000000 : ℝ)*X 1 0+(-391270741/2000000000 : ℝ)*X 1 1+(5411753859/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305688763/10000000000 : ℝ)*X 2 0+(5411753853/10000000000 : ℝ)*X 2 1+(-1956353711/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4324816469/10000000000 : ℝ)*X 0 0+(4502794857/10000000000 : ℝ)*X 0 1+(4153461547/10000000000 : ℝ)*X 0 2+(4324816469/10000000000 : ℝ)*X 1 0+(4502794857/10000000000 : ℝ)*X 1 1+(4153461547/10000000000 : ℝ)*X 1 2+(4324816469/10000000000 : ℝ)*X 2 0+(4502794857/10000000000 : ℝ)*X 2 1+(4153461547/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3575578582267970998062554853/593500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1131398221/100000000000000 : ℝ)*(base19) + (129234307/12500000000000 : ℝ)*(base23) + (2999143/6250000000000 : ℝ)*(lower2) + (79022163/50000000000000 : ℝ)*(upper3) + (532551/781250000000 : ℝ)*(upper5) + (220265641536573/5000000000000 : ℝ)*(major0) + (220265641536573/5000000000000 : ℝ)*(major1) + (4405312830731461/100000000000000 : ℝ)*(major2) + (2984273900122483/50000000000000 : ℝ)*(sp0) + (2984284875194283/50000000000000 : ℝ)*(sp1) + (5968569847912331/100000000000000 : ℝ)*(sp2) + (71051050562653/2500000000000 : ℝ)*(sp3) + (1154077091/5000000000000 : ℝ)*(sp4) + (1255635121/10000000000000 : ℝ)*(sp7) + (284205457885733/10000000000000 : ℝ)*(f.failure) + (5968570881786787/100000000000000 : ℝ)*(f.sum) + (35082826457001/5935000000000000000000000000 : ℝ)*base65 + (343481914166889037/59350000000000000000000000000000 : ℝ)*base67 + (23882615202679334309/1187000000000000000000000000000000 : ℝ)*base69 + (20564198381089037/59350000000000000000000000000000 : ℝ)*base71 + (40937144060971/5935000000000000000000000000 : ℝ)*base73 + (12811102702921334309/1187000000000000000000000000000000 : ℝ)*base75 + (656606613910729037/59350000000000000000000000000000 : ℝ)*base77 + (324787897384420963/59350000000000000000000000000000 : ℝ)*base80 + (3539581637617/593500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (142897/31250000000000000000 : ℝ)*base90 + (142897/31250000000000000000 : ℝ)*base92 + (455397/31250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (555307422766740192785341887/74187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (253001107/20000000000000 : ℝ)*(base19) + (687232037/50000000000000 : ℝ)*(base23) + (37531989/25000000000000 : ℝ)*(upper3) + (1009147/2000000000000 : ℝ)*(lower4) + (155461957/100000000000000 : ℝ)*(upper5) + (554643963432241/12500000000000 : ℝ)*(major0) + (554643963432241/12500000000000 : ℝ)*(major1) + (554643963432241/12500000000000 : ℝ)*(major2) + (5198140461/20000000000000 : ℝ)*(sp1) + (27615312607/100000000000000 : ℝ)*(sp2) + (6011707973691581/100000000000000 : ℝ)*(sp4) + (6011680717983741/100000000000000 : ℝ)*(sp5) + (60116789839149/1000000000000 : ℝ)*(sp6) + (1431297595858993/50000000000000 : ℝ)*(sp7) + (1431297595858993/50000000000000 : ℝ)*(f.failure) + (6011707973691581/100000000000000 : ℝ)*(f.sum) + (4343637802947/2967500000000000000000000000 : ℝ)*base66 + (400128728302381871/148375000000000000000000000000000 : ℝ)*base68 + (391511893948006871/148375000000000000000000000000000 : ℝ)*base70 + (1030133528479868129/148375000000000000000000000000000 : ℝ)*base71 + (47395687515309/5935000000000000000000000000 : ℝ)*base74 + (1584583115809868129/148375000000000000000000000000000 : ℝ)*base75 + (541439993236006871/148375000000000000000000000000000 : ℝ)*base78 + (620487676754381871/148375000000000000000000000000000 : ℝ)*base80 + (18178814242317/2967500000000000000000000000 : ℝ)*base82 + (961763/156250000000000000000 : ℝ)*base89 + (961763/156250000000000000000 : ℝ)*base91 + (961763/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1349_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4843891/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14719/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5579/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2233/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1839/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1349_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1349_s7_0 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2037941207/10000000000 : ℝ)*x 0 + (1082460001/2000000000 : ℝ)*x 1 + (5244865179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2037941207/10000000000 : ℝ)^4309 ≤ (12412318591277/100000000000000 : ℝ)^3285 := by
    have hnat : (2037941207 : ℕ)^4309*100000000000000^3285 ≤ 12412318591277^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2037941207 10000000000 12412318591277 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082460001/2000000000 : ℝ)^4309 ≤ (22348155065709/50000000000000 : ℝ)^3285 := by
    have hnat : (1082460001 : ℕ)^4309*50000000000000^3285 ≤ 22348155065709^3285*2000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082460001 2000000000 22348155065709 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244865179/10000000000 : ℝ)^4309 ≤ (42891371259811/100000000000000 : ℝ)^3285 := by
    have hnat : (5244865179 : ℕ)^4309*100000000000000^3285 ≤ 42891371259811^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244865179 10000000000 42891371259811 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2037941207/10000000000 : ℝ), (1082460001/2000000000 : ℝ), (5244865179/10000000000 : ℝ)] ![(12412318591277/100000000000000 : ℝ), (22348155065709/50000000000000 : ℝ), (42891371259811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2037941207/10000000000 : ℝ)|^4309 ≤ (12412318591277/100000000000000 : ℝ)^3285
        have hw : |(-2037941207/10000000000 : ℝ)|=(2037941207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082460001/2000000000 : ℝ)|^4309 ≤ (22348155065709/50000000000000 : ℝ)^3285
        have hw : |(1082460001/2000000000 : ℝ)|=(1082460001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244865179/10000000000 : ℝ)|^4309 ≤ (42891371259811/100000000000000 : ℝ)^3285
        have hw : |(5244865179/10000000000 : ℝ)|=(5244865179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s7_1 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337216263/2500000000 : ℝ)*x 0 + (-2123244027/10000000000 : ℝ)*x 1 + (1048973037/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337216263/2500000000 : ℝ)^4309 ≤ (1760416245743/4000000000000 : ℝ)^3285 := by
    have hnat : (1337216263 : ℕ)^4309*4000000000000^3285 ≤ 1760416245743^3285*2500000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337216263 2500000000 1760416245743 4000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2123244027/10000000000 : ℝ)^4309 ≤ (13098222522019/100000000000000 : ℝ)^3285 := by
    have hnat : (2123244027 : ℕ)^4309*100000000000000^3285 ≤ 13098222522019^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123244027 10000000000 13098222522019 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048973037/2000000000 : ℝ)^4309 ≤ (42891371324173/100000000000000 : ℝ)^3285 := by
    have hnat : (1048973037 : ℕ)^4309*100000000000000^3285 ≤ 42891371324173^3285*2000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048973037 2000000000 42891371324173 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337216263/2500000000 : ℝ), (-2123244027/10000000000 : ℝ), (1048973037/2000000000 : ℝ)] ![(1760416245743/4000000000000 : ℝ), (13098222522019/100000000000000 : ℝ), (42891371324173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337216263/2500000000 : ℝ)|^4309 ≤ (1760416245743/4000000000000 : ℝ)^3285
        have hw : |(1337216263/2500000000 : ℝ)|=(1337216263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2123244027/10000000000 : ℝ)|^4309 ≤ (13098222522019/100000000000000 : ℝ)^3285
        have hw : |(-2123244027/10000000000 : ℝ)|=(2123244027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048973037/2000000000 : ℝ)|^4309 ≤ (42891371324173/100000000000000 : ℝ)^3285
        have hw : |(1048973037/2000000000 : ℝ)|=(1048973037/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s7_2 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674432529/5000000000 : ℝ)*x 0 + (209794607/400000000 : ℝ)*x 1 + (-4146961/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674432529/5000000000 : ℝ)^4309 ≤ (11002601552083/25000000000000 : ℝ)^3285 := by
    have hnat : (2674432529 : ℕ)^4309*25000000000000^3285 ≤ 11002601552083^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674432529 5000000000 11002601552083 25000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209794607/400000000 : ℝ)^4309 ≤ (42891371216903/100000000000000 : ℝ)^3285 := by
    have hnat : (209794607 : ℕ)^4309*100000000000000^3285 ≤ 42891371216903^3285*400000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209794607 400000000 42891371216903 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4146961/19531250 : ℝ)^4309 ≤ (13098222562479/100000000000000 : ℝ)^3285 := by
    have hnat : (4146961 : ℕ)^4309*100000000000000^3285 ≤ 13098222562479^3285*19531250^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4146961 19531250 13098222562479 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674432529/5000000000 : ℝ), (209794607/400000000 : ℝ), (-4146961/19531250 : ℝ)] ![(11002601552083/25000000000000 : ℝ), (42891371216903/100000000000000 : ℝ), (13098222562479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674432529/5000000000 : ℝ)|^4309 ≤ (11002601552083/25000000000000 : ℝ)^3285
        have hw : |(2674432529/5000000000 : ℝ)|=(2674432529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209794607/400000000 : ℝ)|^4309 ≤ (42891371216903/100000000000000 : ℝ)^3285
        have hw : |(209794607/400000000 : ℝ)|=(209794607/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4146961/19531250 : ℝ)|^4309 ≤ (13098222562479/100000000000000 : ℝ)^3285
        have hw : |(-4146961/19531250 : ℝ)|=(4146961/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s7_3 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4324794947/10000000000 : ℝ)*x 0 + (830462071/2000000000 : ℝ)*x 1 + (4503938591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4324794947/10000000000 : ℝ)^4309 ≤ (6660682172627/20000000000000 : ℝ)^3285 := by
    have hnat : (4324794947 : ℕ)^4309*20000000000000^3285 ≤ 6660682172627^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4324794947 10000000000 6660682172627 20000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (830462071/2000000000 : ℝ)^4309 ≤ (31572075166623/100000000000000 : ℝ)^3285 := by
    have hnat : (830462071 : ℕ)^4309*100000000000000^3285 ≤ 31572075166623^3285*2000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830462071 2000000000 31572075166623 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4503938591/10000000000 : ℝ)^4309 ≤ (35124513961337/100000000000000 : ℝ)^3285 := by
    have hnat : (4503938591 : ℕ)^4309*100000000000000^3285 ≤ 35124513961337^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503938591 10000000000 35124513961337 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4324794947/10000000000 : ℝ), (830462071/2000000000 : ℝ), (4503938591/10000000000 : ℝ)] ![(6660682172627/20000000000000 : ℝ), (31572075166623/100000000000000 : ℝ), (35124513961337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4324794947/10000000000 : ℝ)|^4309 ≤ (6660682172627/20000000000000 : ℝ)^3285
        have hw : |(4324794947/10000000000 : ℝ)|=(4324794947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(830462071/2000000000 : ℝ)|^4309 ≤ (31572075166623/100000000000000 : ℝ)^3285
        have hw : |(830462071/2000000000 : ℝ)|=(830462071/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4503938591/10000000000 : ℝ)|^4309 ≤ (35124513961337/100000000000000 : ℝ)^3285
        have hw : |(4503938591/10000000000 : ℝ)|=(4503938591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s7_4 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2037953347/10000000000 : ℝ)*x 0 + (5245464609/10000000000 : ℝ)*x 1 + (1352924361/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2037953347/10000000000 : ℝ)^4309 ≤ (3103103895013/25000000000000 : ℝ)^3285 := by
    have hnat : (2037953347 : ℕ)^4309*25000000000000^3285 ≤ 3103103895013^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2037953347 10000000000 3103103895013 25000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245464609/10000000000 : ℝ)^4309 ≤ (8579560287377/20000000000000 : ℝ)^3285 := by
    have hnat : (5245464609 : ℕ)^4309*20000000000000^3285 ≤ 8579560287377^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245464609 10000000000 8579560287377 20000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352924361/2500000000 : ℝ)^4309 ≤ (8937956593819/20000000000000 : ℝ)^3285 := by
    have hnat : (1352924361 : ℕ)^4309*20000000000000^3285 ≤ 8937956593819^3285*2500000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352924361 2500000000 8937956593819 20000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2037953347/10000000000 : ℝ), (5245464609/10000000000 : ℝ), (1352924361/2500000000 : ℝ)] ![(3103103895013/25000000000000 : ℝ), (8579560287377/20000000000000 : ℝ), (8937956593819/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2037953347/10000000000 : ℝ)|^4309 ≤ (3103103895013/25000000000000 : ℝ)^3285
        have hw : |(-2037953347/10000000000 : ℝ)|=(2037953347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245464609/10000000000 : ℝ)|^4309 ≤ (8579560287377/20000000000000 : ℝ)^3285
        have hw : |(5245464609/10000000000 : ℝ)|=(5245464609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352924361/2500000000 : ℝ)|^4309 ≤ (8937956593819/20000000000000 : ℝ)^3285
        have hw : |(1352924361/2500000000 : ℝ)|=(1352924361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s7_5 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652851527/5000000000 : ℝ)*x 0 + (-30568933/156250000 : ℝ)*x 1 + (2705848707/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652851527/5000000000 : ℝ)^4309 ≤ (8709030704789/20000000000000 : ℝ)^3285 := by
    have hnat : (2652851527 : ℕ)^4309*20000000000000^3285 ≤ 8709030704789^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652851527 5000000000 8709030704789 20000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (30568933/156250000 : ℝ)^4309 ≤ (5882531912893/50000000000000 : ℝ)^3285 := by
    have hnat : (30568933 : ℕ)^4309*50000000000000^3285 ≤ 5882531912893^3285*156250000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30568933 156250000 5882531912893 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705848707/5000000000 : ℝ)^4309 ≤ (4468978264413/10000000000000 : ℝ)^3285 := by
    have hnat : (2705848707 : ℕ)^4309*10000000000000^3285 ≤ 4468978264413^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705848707 5000000000 4468978264413 10000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652851527/5000000000 : ℝ), (-30568933/156250000 : ℝ), (2705848707/5000000000 : ℝ)] ![(8709030704789/20000000000000 : ℝ), (5882531912893/50000000000000 : ℝ), (4468978264413/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652851527/5000000000 : ℝ)|^4309 ≤ (8709030704789/20000000000000 : ℝ)^3285
        have hw : |(2652851527/5000000000 : ℝ)|=(2652851527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-30568933/156250000 : ℝ)|^4309 ≤ (5882531912893/50000000000000 : ℝ)^3285
        have hw : |(-30568933/156250000 : ℝ)|=(30568933/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705848707/5000000000 : ℝ)|^4309 ≤ (4468978264413/10000000000000 : ℝ)^3285
        have hw : |(2705848707/5000000000 : ℝ)|=(2705848707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s7_6 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305703069/10000000000 : ℝ)*x 0 + (43293579/80000000 : ℝ)*x 1 + (-61137867/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305703069/10000000000 : ℝ)^4309 ≤ (43545153685429/100000000000000 : ℝ)^3285 := by
    have hnat : (5305703069 : ℕ)^4309*100000000000000^3285 ≤ 43545153685429^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305703069 10000000000 43545153685429 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43293579/80000000 : ℝ)^4309 ≤ (1787591288867/4000000000000 : ℝ)^3285 := by
    have hnat : (43293579 : ℕ)^4309*4000000000000^3285 ≤ 1787591288867^3285*80000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43293579 80000000 1787591288867 4000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (61137867/312500000 : ℝ)^4309 ≤ (11765064078207/100000000000000 : ℝ)^3285 := by
    have hnat : (61137867 : ℕ)^4309*100000000000000^3285 ≤ 11765064078207^3285*312500000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61137867 312500000 11765064078207 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305703069/10000000000 : ℝ), (43293579/80000000 : ℝ), (-61137867/312500000 : ℝ)] ![(43545153685429/100000000000000 : ℝ), (1787591288867/4000000000000 : ℝ), (11765064078207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305703069/10000000000 : ℝ)|^4309 ≤ (43545153685429/100000000000000 : ℝ)^3285
        have hw : |(5305703069/10000000000 : ℝ)|=(5305703069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(43293579/80000000 : ℝ)|^4309 ≤ (1787591288867/4000000000000 : ℝ)^3285
        have hw : |(43293579/80000000 : ℝ)|=(43293579/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-61137867/312500000 : ℝ)|^4309 ≤ (11765064078207/100000000000000 : ℝ)^3285
        have hw : |(-61137867/312500000 : ℝ)|=(61137867/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s7_7 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4324820351/10000000000 : ℝ)*x 0 + (4502679667/10000000000 : ℝ)*x 1 + (207678787/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4324820351/10000000000 : ℝ)^4309 ≤ (1665183373457/5000000000000 : ℝ)^3285 := by
    have hnat : (4324820351 : ℕ)^4309*5000000000000^3285 ≤ 1665183373457^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4324820351 10000000000 1665183373457 5000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4502679667/10000000000 : ℝ)^4309 ≤ (35111636223659/100000000000000 : ℝ)^3285 := by
    have hnat : (4502679667 : ℕ)^4309*100000000000000^3285 ≤ 35111636223659^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502679667 10000000000 35111636223659 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207678787/500000000 : ℝ)^4309 ≤ (31584696282371/100000000000000 : ℝ)^3285 := by
    have hnat : (207678787 : ℕ)^4309*100000000000000^3285 ≤ 31584696282371^3285*500000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207678787 500000000 31584696282371 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4324820351/10000000000 : ℝ), (4502679667/10000000000 : ℝ), (207678787/500000000 : ℝ)] ![(1665183373457/5000000000000 : ℝ), (35111636223659/100000000000000 : ℝ), (31584696282371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4324820351/10000000000 : ℝ)|^4309 ≤ (1665183373457/5000000000000 : ℝ)^3285
        have hw : |(4324820351/10000000000 : ℝ)|=(4324820351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4502679667/10000000000 : ℝ)|^4309 ≤ (35111636223659/100000000000000 : ℝ)^3285
        have hw : |(4502679667/10000000000 : ℝ)|=(4502679667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(207678787/500000000 : ℝ)|^4309 ≤ (31584696282371/100000000000000 : ℝ)^3285
        have hw : |(207678787/500000000 : ℝ)|=(207678787/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1349_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4843891/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1839/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2233/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5583/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14711/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1839/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2233/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1839/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2233/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1839/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2233/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1839/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2233/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1839/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2233/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1839/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2233/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2233/20000 : ℝ) ^ (1077/256 : ℝ) ≤ (2467470223438341/25000000000000000000 : ℝ) := by
    have hpowers : (2233/20000 : ℝ)^1077 ≤ (2467470223438341/25000000000000000000 : ℝ)^256 := by
      have hnat : (2233 : ℕ)^1077*25000000000000000000^256 ≤ 2467470223438341^256*20000^1077 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2233 20000 2467470223438341 25000000000000000000 1077 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2233/20000 : ℝ)) (X := (2467470223438341/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have hpowhi : (1839/12500 : ℝ) ^ (1077/256 : ℝ) ≤ (1969014513290261/6250000000000000000 : ℝ) := by
    have hpowers : (1839/12500 : ℝ)^1077 ≤ (1969014513290261/6250000000000000000 : ℝ)^256 := by
      have hnat : (1839 : ℕ)^1077*6250000000000000000^256 ≤ 1969014513290261^256*12500^1077 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1839 12500 1969014513290261 6250000000000000000 1077 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1839/12500 : ℝ)) (X := (1969014513290261/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502467470223438341/12500000000000000000 : ℝ) ≤ (500023458676201/500000000000000 : ℝ) ^ (1077/256 : ℝ) := by
    have hpowers : (12502467470223438341/12500000000000000000 : ℝ)^256 ≤ (500023458676201/500000000000000 : ℝ)^1077 := by
      have hnat : (12502467470223438341 : ℕ)^256*500000000000000^1077 ≤ 500023458676201^1077*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502467470223438341 12500000000000000000 500023458676201 500000000000000 256 1077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500023458676201/500000000000000 : ℝ)) (X := (12502467470223438341/12500000000000000000 : ℝ)) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (5002068705655319877/5000000000000000000 : ℝ) ≤ (625061456029827/625000000000000 : ℝ) ^ (1077/256 : ℝ) := by
    have hpowers : (5002068705655319877/5000000000000000000 : ℝ)^256 ≤ (625061456029827/625000000000000 : ℝ)^1077 := by
      have hnat : (5002068705655319877 : ℕ)^256*625000000000000^1077 ≤ 625061456029827^1077*5000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002068705655319877 5000000000000000000 625061456029827 625000000000000 256 1077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625061456029827/625000000000000 : ℝ)) (X := (5002068705655319877/5000000000000000000 : ℝ)) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (3126969014513290261/3125000000000000000 : ℝ) ≤ (2500374354857611/2500000000000000 : ℝ) ^ (1077/256 : ℝ) := by
    have hpowers : (3126969014513290261/3125000000000000000 : ℝ)^256 ≤ (2500374354857611/2500000000000000 : ℝ)^1077 := by
      have hnat : (3126969014513290261 : ℕ)^256*2500000000000000^1077 ≤ 2500374354857611^1077*3125000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126969014513290261 3125000000000000000 2500374354857611 2500000000000000 256 1077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500374354857611/2500000000000000 : ℝ)) (X := (3126969014513290261/3125000000000000000 : ℝ)) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2467470223438341/25000000000000000000 : ℝ) ≤ ((1773009189647223749/1773500000000000000 : ℝ)+2*(128530738303/88675000000000 : ℝ)*(2233/20000 : ℝ))^(1077/256 : ℝ) := by
    rw [show (1773009189647223749/1773500000000000000 : ℝ)+2*(128530738303/88675000000000 : ℝ)*(2233/20000 : ℝ)=(500023458676201/500000000000000 : ℝ) by norm_num, show 1+2*(2467470223438341/25000000000000000000 : ℝ)=(12502467470223438341/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1969014513290261/6250000000000000000 : ℝ)+(2467470223438341/25000000000000000000 : ℝ) ≤ ((1773009189647223749/1773500000000000000 : ℝ)+(128530738303/88675000000000 : ℝ)*((1839/12500 : ℝ)+(2233/20000 : ℝ)))^(1077/256 : ℝ) := by
    rw [show (1773009189647223749/1773500000000000000 : ℝ)+(128530738303/88675000000000 : ℝ)*((1839/12500 : ℝ)+(2233/20000 : ℝ))=(625061456029827/625000000000000 : ℝ) by norm_num, show 1+(1969014513290261/6250000000000000000 : ℝ)+(2467470223438341/25000000000000000000 : ℝ)=(5002068705655319877/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1969014513290261/6250000000000000000 : ℝ) ≤ ((1773009189647223749/1773500000000000000 : ℝ)+2*(128530738303/88675000000000 : ℝ)*(1839/12500 : ℝ))^(1077/256 : ℝ) := by
    rw [show (1773009189647223749/1773500000000000000 : ℝ)+2*(128530738303/88675000000000 : ℝ)*(1839/12500 : ℝ)=(2500374354857611/2500000000000000 : ℝ) by norm_num, show 1+2*(1969014513290261/6250000000000000000 : ℝ)=(3126969014513290261/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1773009189647223749/1773500000000000000 : ℝ)*(X 1 0+X 2 0)+(128530738303/88675000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1077/256 : ℝ)) (lo := (2233/20000 : ℝ)) (hi := (1839/12500 : ℝ)) (c := (1773009189647223749/1773500000000000000 : ℝ)) (alpha := (128530738303/88675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1773009189647223749/1773500000000000000 : ℝ)*(X 0 1+X 2 1)+(128530738303/88675000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1077/256 : ℝ)) (lo := (2233/20000 : ℝ)) (hi := (1839/12500 : ℝ)) (c := (1773009189647223749/1773500000000000000 : ℝ)) (alpha := (128530738303/88675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1773009189647223749/1773500000000000000 : ℝ)*(X 0 2+X 1 2)+(128530738303/88675000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1077/256 : ℝ)) (lo := (2233/20000 : ℝ)) (hi := (1839/12500 : ℝ)) (c := (1773009189647223749/1773500000000000000 : ℝ)) (alpha := (128530738303/88675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2037941207/10000000000 : ℝ)*X 0 0+(1082460001/2000000000 : ℝ)*X 0 1+(5244865179/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337216263/2500000000 : ℝ)*X 1 0+(-2123244027/10000000000 : ℝ)*X 1 1+(1048973037/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674432529/5000000000 : ℝ)*X 2 0+(209794607/400000000 : ℝ)*X 2 1+(-4146961/19531250 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4324794947/10000000000 : ℝ)*X 0 0+(830462071/2000000000 : ℝ)*X 0 1+(4503938591/10000000000 : ℝ)*X 0 2+(4324794947/10000000000 : ℝ)*X 1 0+(830462071/2000000000 : ℝ)*X 1 1+(4503938591/10000000000 : ℝ)*X 1 2+(4324794947/10000000000 : ℝ)*X 2 0+(830462071/2000000000 : ℝ)*X 2 1+(4503938591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2037953347/10000000000 : ℝ)*X 0 0+(5245464609/10000000000 : ℝ)*X 0 1+(1352924361/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652851527/5000000000 : ℝ)*X 1 0+(-30568933/156250000 : ℝ)*X 1 1+(2705848707/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305703069/10000000000 : ℝ)*X 2 0+(43293579/80000000 : ℝ)*X 2 1+(-61137867/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4324820351/10000000000 : ℝ)*X 0 0+(4502679667/10000000000 : ℝ)*X 0 1+(207678787/500000000 : ℝ)*X 0 2+(4324820351/10000000000 : ℝ)*X 1 0+(4502679667/10000000000 : ℝ)*X 1 1+(207678787/500000000 : ℝ)*X 1 2+(4324820351/10000000000 : ℝ)*X 2 0+(4502679667/10000000000 : ℝ)*X 2 1+(207678787/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (328505256013691369109735003/44337500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1374003917/100000000000000 : ℝ)*(base19) + (323649203/25000000000000 : ℝ)*(base23) + (23028653/50000000000000 : ℝ)*(lower2) + (91914009/50000000000000 : ℝ)*(upper3) + (28828067/25000000000000 : ℝ)*(upper5) + (4408235863112499/100000000000000 : ℝ)*(major0) + (4408235863112499/100000000000000 : ℝ)*(major1) + (352658869049/8000000000 : ℝ)*(major2) + (1194500553869931/20000000000000 : ℝ)*(sp0) + (298626487697107/5000000000000 : ℝ)*(sp1) + (1194505966669849/20000000000000 : ℝ)*(sp2) + (568785154535683/20000000000000 : ℝ)*(sp3) + (28358596401/100000000000000 : ℝ)*(sp4) + (7289313647/50000000000000 : ℝ)*(sp7) + (710985087826427/25000000000000 : ℝ)*(f.failure) + (746566390993257/12500000000000 : ℝ)*(f.sum) + (16062656793851/17735000000000000000000000000 : ℝ)*base66 + (897363394994911249/177350000000000000000000000000000 : ℝ)*base68 + (530206226309921/70940000000000000000000000000 : ℝ)*base69 + (591236291789111249/177350000000000000000000000000000 : ℝ)*base72 + (3090021730211/17735000000000000000000000000 : ℝ)*base74 + (254538095945581/70940000000000000000000000000 : ℝ)*base75 + (1979813105640671249/177350000000000000000000000000000 : ℝ)*base78 + (3515761805804821249/177350000000000000000000000000000 : ℝ)*base80 + (16204258487813/17735000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (536293/78125000000000000000 : ℝ)*base90 + (536293/78125000000000000000 : ℝ)*base92 + (1317543/78125000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (387556677648684383747413863/44337500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1835225791/100000000000000 : ℝ)*(base19) + (952887851/50000000000000 : ℝ)*(base23) + (156725419/25000000000000 : ℝ)*(lower1) + (6090851/3125000000000 : ℝ)*(upper3) + (3622223/12500000000000 : ℝ)*(lower4) + (100167567/50000000000000 : ℝ)*(upper5) + (2220019811305871/50000000000000 : ℝ)*(major0) + (2220019811305871/50000000000000 : ℝ)*(major1) + (2220019811305871/50000000000000 : ℝ)*(major2) + (131950263/100000000000000 : ℝ)*(sp1) + (1503905161326157/25000000000000 : ℝ)*(sp4) + (3007809339064287/50000000000000 : ℝ)*(sp5) + (6015618739528927/100000000000000 : ℝ)*(sp6) + (358057288568779/12500000000000 : ℝ)*(sp7) + (358057288568779/12500000000000 : ℝ)*(f.failure) + (1503905161326157/25000000000000 : ℝ)*(f.sum) + (14117792157261/4433750000000000000000000000 : ℝ)*base65 + (255555266547290379/88675000000000000000000000000000 : ℝ)*base67 + (211510454700990379/88675000000000000000000000000000 : ℝ)*base69 + (255670374855390379/88675000000000000000000000000000 : ℝ)*base71 + (65497158538379/17735000000000000000000000000 : ℝ)*base73 + (1374338498749165379/88675000000000000000000000000000 : ℝ)*base75 + (733836506974034621/88675000000000000000000000000000 : ℝ)*base78 + (1055465252093484621/88675000000000000000000000000000 : ℝ)*base80 + (19908188500273/2216875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (239661/39062500000000000000 : ℝ)*base90 + (239661/39062500000000000000 : ℝ)*base92 + (239661/39062500000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1349_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4843891/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1839/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2233/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5583/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14711/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1349_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1349_box_0 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-93561837/500000000 : ℝ)*x 0 + (5389649051/10000000000 : ℝ)*x 1 + (5389648907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (93561837/500000000 : ℝ)^4309 ≤ (11097796316151/100000000000000 : ℝ)^3285 := by
    have hnat : (93561837 : ℕ)^4309*100000000000000^3285 ≤ 11097796316151^3285*500000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93561837 500000000 11097796316151 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5389649051/10000000000 : ℝ)^4309 ≤ (44451102615133/100000000000000 : ℝ)^3285 := by
    have hnat : (5389649051 : ℕ)^4309*100000000000000^3285 ≤ 44451102615133^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389649051 10000000000 44451102615133 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5389648907/10000000000 : ℝ)^4309 ≤ (44451101057283/100000000000000 : ℝ)^3285 := by
    have hnat : (5389648907 : ℕ)^4309*100000000000000^3285 ≤ 44451101057283^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389648907 10000000000 44451101057283 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-93561837/500000000 : ℝ), (5389649051/10000000000 : ℝ), (5389648907/10000000000 : ℝ)] ![(11097796316151/100000000000000 : ℝ), (44451102615133/100000000000000 : ℝ), (44451101057283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-93561837/500000000 : ℝ)|^4309 ≤ (11097796316151/100000000000000 : ℝ)^3285
        have hw : |(-93561837/500000000 : ℝ)|=(93561837/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5389649051/10000000000 : ℝ)|^4309 ≤ (44451102615133/100000000000000 : ℝ)^3285
        have hw : |(5389649051/10000000000 : ℝ)|=(5389649051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5389648907/10000000000 : ℝ)|^4309 ≤ (44451101057283/100000000000000 : ℝ)^3285
        have hw : |(5389648907/10000000000 : ℝ)|=(5389648907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_box_1 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (660657287/1250000000 : ℝ)*x 0 + (-1007145417/5000000000 : ℝ)*x 1 + (5389648811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660657287/1250000000 : ℝ)^4309 ≤ (43325185860929/100000000000000 : ℝ)^3285 := by
    have hnat : (660657287 : ℕ)^4309*100000000000000^3285 ≤ 43325185860929^3285*1250000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660657287 1250000000 43325185860929 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1007145417/5000000000 : ℝ)^4309 ≤ (190995532837/1562500000000 : ℝ)^3285 := by
    have hnat : (1007145417 : ℕ)^4309*1562500000000^3285 ≤ 190995532837^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007145417 5000000000 190995532837 1562500000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5389648811/10000000000 : ℝ)^4309 ≤ (11112775004679/25000000000000 : ℝ)^3285 := by
    have hnat : (5389648811 : ℕ)^4309*25000000000000^3285 ≤ 11112775004679^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389648811 10000000000 11112775004679 25000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660657287/1250000000 : ℝ), (-1007145417/5000000000 : ℝ), (5389648811/10000000000 : ℝ)] ![(43325185860929/100000000000000 : ℝ), (190995532837/1562500000000 : ℝ), (11112775004679/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660657287/1250000000 : ℝ)|^4309 ≤ (43325185860929/100000000000000 : ℝ)^3285
        have hw : |(660657287/1250000000 : ℝ)|=(660657287/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1007145417/5000000000 : ℝ)|^4309 ≤ (190995532837/1562500000000 : ℝ)^3285
        have hw : |(-1007145417/5000000000 : ℝ)|=(1007145417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5389648811/10000000000 : ℝ)|^4309 ≤ (11112775004679/25000000000000 : ℝ)^3285
        have hw : |(5389648811/10000000000 : ℝ)|=(5389648811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_box_2 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5285258169/10000000000 : ℝ)*x 0 + (2694824501/5000000000 : ℝ)*x 1 + (-1007145373/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285258169/10000000000 : ℝ)^4309 ≤ (43325184495343/100000000000000 : ℝ)^3285 := by
    have hnat : (5285258169 : ℕ)^4309*100000000000000^3285 ≤ 43325184495343^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285258169 10000000000 43325184495343 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2694824501/5000000000 : ℝ)^4309 ≤ (44451102085031/100000000000000 : ℝ)^3285 := by
    have hnat : (2694824501 : ℕ)^4309*100000000000000^3285 ≤ 44451102085031^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694824501 5000000000 44451102085031 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1007145373/5000000000 : ℝ)^4309 ≤ (6111856700537/50000000000000 : ℝ)^3285 := by
    have hnat : (1007145373 : ℕ)^4309*50000000000000^3285 ≤ 6111856700537^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007145373 5000000000 6111856700537 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285258169/10000000000 : ℝ), (2694824501/5000000000 : ℝ), (-1007145373/5000000000 : ℝ)] ![(43325184495343/100000000000000 : ℝ), (44451102085031/100000000000000 : ℝ), (6111856700537/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285258169/10000000000 : ℝ)|^4309 ≤ (43325184495343/100000000000000 : ℝ)^3285
        have hw : |(5285258169/10000000000 : ℝ)|=(5285258169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2694824501/5000000000 : ℝ)|^4309 ≤ (44451102085031/100000000000000 : ℝ)^3285
        have hw : |(2694824501/5000000000 : ℝ)|=(2694824501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1007145373/5000000000 : ℝ)|^4309 ≤ (6111856700537/50000000000000 : ℝ)^3285
        have hw : |(-1007145373/5000000000 : ℝ)|=(1007145373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_box_3 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (27955149/62500000 : ℝ)*x 0 + (4254654159/10000000000 : ℝ)*x 1 + (1063663577/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (27955149/62500000 : ℝ)^4309 ≤ (8701641380573/25000000000000 : ℝ)^3285 := by
    have hnat : (27955149 : ℕ)^4309*25000000000000^3285 ≤ 8701641380573^3285*62500000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27955149 62500000 8701641380573 25000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4254654159/10000000000 : ℝ)^4309 ≤ (6519343295877/20000000000000 : ℝ)^3285 := by
    have hnat : (4254654159 : ℕ)^4309*20000000000000^3285 ≤ 6519343295877^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4254654159 10000000000 6519343295877 20000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1063663577/2500000000 : ℝ)^4309 ≤ (16298358988391/50000000000000 : ℝ)^3285 := by
    have hnat : (1063663577 : ℕ)^4309*50000000000000^3285 ≤ 16298358988391^3285*2500000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063663577 2500000000 16298358988391 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(27955149/62500000 : ℝ), (4254654159/10000000000 : ℝ), (1063663577/2500000000 : ℝ)] ![(8701641380573/25000000000000 : ℝ), (6519343295877/20000000000000 : ℝ), (16298358988391/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(27955149/62500000 : ℝ)|^4309 ≤ (8701641380573/25000000000000 : ℝ)^3285
        have hw : |(27955149/62500000 : ℝ)|=(27955149/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4254654159/10000000000 : ℝ)|^4309 ≤ (6519343295877/20000000000000 : ℝ)^3285
        have hw : |(4254654159/10000000000 : ℝ)|=(4254654159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1063663577/2500000000 : ℝ)|^4309 ≤ (16298358988391/50000000000000 : ℝ)^3285
        have hw : |(1063663577/2500000000 : ℝ)|=(1063663577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_box_4 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2207395451/10000000000 : ℝ)*x 0 + (2632539243/5000000000 : ℝ)*x 1 + (2632539311/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2207395451/10000000000 : ℝ)^4309 ≤ (3445835255379/25000000000000 : ℝ)^3285 := by
    have hnat : (2207395451 : ℕ)^4309*25000000000000^3285 ≤ 3445835255379^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207395451 10000000000 3445835255379 25000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632539243/5000000000 : ℝ)^4309 ≤ (43108328753207/100000000000000 : ℝ)^3285 := by
    have hnat : (2632539243 : ℕ)^4309*100000000000000^3285 ≤ 43108328753207^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632539243 5000000000 43108328753207 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632539311/5000000000 : ℝ)^4309 ≤ (673567659591/1562500000000 : ℝ)^3285 := by
    have hnat : (2632539311 : ℕ)^4309*1562500000000^3285 ≤ 673567659591^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632539311 5000000000 673567659591 1562500000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2207395451/10000000000 : ℝ), (2632539243/5000000000 : ℝ), (2632539311/5000000000 : ℝ)] ![(3445835255379/25000000000000 : ℝ), (43108328753207/100000000000000 : ℝ), (673567659591/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2207395451/10000000000 : ℝ)|^4309 ≤ (3445835255379/25000000000000 : ℝ)^3285
        have hw : |(-2207395451/10000000000 : ℝ)|=(2207395451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632539243/5000000000 : ℝ)|^4309 ≤ (43108328753207/100000000000000 : ℝ)^3285
        have hw : |(2632539243/5000000000 : ℝ)|=(2632539243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632539311/5000000000 : ℝ)|^4309 ≤ (673567659591/1562500000000 : ℝ)^3285
        have hw : |(2632539311/5000000000 : ℝ)|=(2632539311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_box_5 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2686364039/5000000000 : ℝ)*x 0 + (-1032163003/5000000000 : ℝ)*x 1 + (2632539299/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686364039/5000000000 : ℝ)^4309 ≤ (22134067171571/50000000000000 : ℝ)^3285 := by
    have hnat : (2686364039 : ℕ)^4309*50000000000000^3285 ≤ 22134067171571^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686364039 5000000000 22134067171571 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1032163003/5000000000 : ℝ)^4309 ≤ (6311767842821/50000000000000 : ℝ)^3285 := by
    have hnat : (1032163003 : ℕ)^4309*50000000000000^3285 ≤ 6311767842821^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032163003 5000000000 6311767842821 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632539299/5000000000 : ℝ)^4309 ≤ (10777082489017/25000000000000 : ℝ)^3285 := by
    have hnat : (2632539299 : ℕ)^4309*25000000000000^3285 ≤ 10777082489017^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632539299 5000000000 10777082489017 25000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686364039/5000000000 : ℝ), (-1032163003/5000000000 : ℝ), (2632539299/5000000000 : ℝ)] ![(22134067171571/50000000000000 : ℝ), (6311767842821/50000000000000 : ℝ), (10777082489017/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686364039/5000000000 : ℝ)|^4309 ≤ (22134067171571/50000000000000 : ℝ)^3285
        have hw : |(2686364039/5000000000 : ℝ)|=(2686364039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1032163003/5000000000 : ℝ)|^4309 ≤ (6311767842821/50000000000000 : ℝ)^3285
        have hw : |(-1032163003/5000000000 : ℝ)|=(1032163003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632539299/5000000000 : ℝ)|^4309 ≤ (10777082489017/25000000000000 : ℝ)^3285
        have hw : |(2632539299/5000000000 : ℝ)|=(2632539299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_box_6 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5372728303/10000000000 : ℝ)*x 0 + (2632539231/5000000000 : ℝ)*x 1 + (-412865177/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5372728303/10000000000 : ℝ)^4309 ≤ (22134068387449/50000000000000 : ℝ)^3285 := by
    have hnat : (5372728303 : ℕ)^4309*50000000000000^3285 ≤ 22134068387449^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5372728303 10000000000 22134068387449 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632539231/5000000000 : ℝ)^4309 ≤ (43108328495451/100000000000000 : ℝ)^3285 := by
    have hnat : (2632539231 : ℕ)^4309*100000000000000^3285 ≤ 43108328495451^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632539231 5000000000 43108328495451 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (412865177/2000000000 : ℝ)^4309 ≤ (12623534715067/100000000000000 : ℝ)^3285 := by
    have hnat : (412865177 : ℕ)^4309*100000000000000^3285 ≤ 12623534715067^3285*2000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412865177 2000000000 12623534715067 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5372728303/10000000000 : ℝ), (2632539231/5000000000 : ℝ), (-412865177/2000000000 : ℝ)] ![(22134068387449/50000000000000 : ℝ), (43108328495451/100000000000000 : ℝ), (12623534715067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5372728303/10000000000 : ℝ)|^4309 ≤ (22134068387449/50000000000000 : ℝ)^3285
        have hw : |(5372728303/10000000000 : ℝ)|=(5372728303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632539231/5000000000 : ℝ)|^4309 ≤ (43108328495451/100000000000000 : ℝ)^3285
        have hw : |(2632539231/5000000000 : ℝ)|=(2632539231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-412865177/2000000000 : ℝ)|^4309 ≤ (12623534715067/100000000000000 : ℝ)^3285
        have hw : |(-412865177/2000000000 : ℝ)|=(412865177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_box_7 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2087915001/5000000000 : ℝ)*x 0 + (88061959/200000000 : ℝ)*x 1 + (440309763/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2087915001/5000000000 : ℝ)^4309 ≤ (7951714722031/25000000000000 : ℝ)^3285 := by
    have hnat : (2087915001 : ℕ)^4309*25000000000000^3285 ≤ 7951714722031^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087915001 5000000000 7951714722031 25000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (88061959/200000000 : ℝ)^4309 ≤ (3409657217173/10000000000000 : ℝ)^3285 := by
    have hnat : (88061959 : ℕ)^4309*10000000000000^3285 ≤ 3409657217173^3285*200000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88061959 200000000 3409657217173 10000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (440309763/1000000000 : ℝ)^4309 ≤ (106551777879/312500000000 : ℝ)^3285 := by
    have hnat : (440309763 : ℕ)^4309*312500000000^3285 ≤ 106551777879^3285*1000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440309763 1000000000 106551777879 312500000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2087915001/5000000000 : ℝ), (88061959/200000000 : ℝ), (440309763/1000000000 : ℝ)] ![(7951714722031/25000000000000 : ℝ), (3409657217173/10000000000000 : ℝ), (106551777879/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2087915001/5000000000 : ℝ)|^4309 ≤ (7951714722031/25000000000000 : ℝ)^3285
        have hw : |(2087915001/5000000000 : ℝ)|=(2087915001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(88061959/200000000 : ℝ)|^4309 ≤ (3409657217173/10000000000000 : ℝ)^3285
        have hw : |(88061959/200000000 : ℝ)|=(88061959/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(440309763/1000000000 : ℝ)|^4309 ≤ (106551777879/312500000000 : ℝ)^3285
        have hw : |(440309763/1000000000 : ℝ)|=(440309763/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_box_8 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2136784113/10000000000 : ℝ)*x 0 + (1294821847/2500000000 : ℝ)*x 1 + (168864569/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2136784113/10000000000 : ℝ)^4309 ≤ (13207897059411/100000000000000 : ℝ)^3285 := by
    have hnat : (2136784113 : ℕ)^4309*100000000000000^3285 ≤ 13207897059411^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136784113 10000000000 13207897059411 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1294821847/2500000000 : ℝ)^4309 ≤ (4218929562509/10000000000000 : ℝ)^3285 := by
    have hnat : (1294821847 : ℕ)^4309*10000000000000^3285 ≤ 4218929562509^3285*2500000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294821847 2500000000 4218929562509 10000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168864569/312500000 : ℝ)^4309 ≤ (44602807306579/100000000000000 : ℝ)^3285 := by
    have hnat : (168864569 : ℕ)^4309*100000000000000^3285 ≤ 44602807306579^3285*312500000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168864569 312500000 44602807306579 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2136784113/10000000000 : ℝ), (1294821847/2500000000 : ℝ), (168864569/312500000 : ℝ)] ![(13207897059411/100000000000000 : ℝ), (4218929562509/10000000000000 : ℝ), (44602807306579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2136784113/10000000000 : ℝ)|^4309 ≤ (13207897059411/100000000000000 : ℝ)^3285
        have hw : |(-2136784113/10000000000 : ℝ)|=(2136784113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1294821847/2500000000 : ℝ)|^4309 ≤ (4218929562509/10000000000000 : ℝ)^3285
        have hw : |(1294821847/2500000000 : ℝ)|=(1294821847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168864569/312500000 : ℝ)|^4309 ≤ (44602807306579/100000000000000 : ℝ)^3285
        have hw : |(168864569/312500000 : ℝ)|=(168864569/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_box_9 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (20607073/39062500 : ℝ)*x 0 + (-200852857/1000000000 : ℝ)*x 1 + (1080733203/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20607073/39062500 : ℝ)^4309 ≤ (10804832195943/25000000000000 : ℝ)^3285 := by
    have hnat : (20607073 : ℕ)^4309*25000000000000^3285 ≤ 10804832195943^3285*39062500^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20607073 39062500 10804832195943 25000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (200852857/1000000000 : ℝ)^4309 ≤ (1522233248503/12500000000000 : ℝ)^3285 := by
    have hnat : (200852857 : ℕ)^4309*12500000000000^3285 ≤ 1522233248503^3285*1000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200852857 1000000000 1522233248503 12500000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080733203/2000000000 : ℝ)^4309 ≤ (5575350652117/12500000000000 : ℝ)^3285 := by
    have hnat : (1080733203 : ℕ)^4309*12500000000000^3285 ≤ 5575350652117^3285*2000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080733203 2000000000 5575350652117 12500000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20607073/39062500 : ℝ), (-200852857/1000000000 : ℝ), (1080733203/2000000000 : ℝ)] ![(10804832195943/25000000000000 : ℝ), (1522233248503/12500000000000 : ℝ), (5575350652117/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20607073/39062500 : ℝ)|^4309 ≤ (10804832195943/25000000000000 : ℝ)^3285
        have hw : |(20607073/39062500 : ℝ)|=(20607073/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-200852857/1000000000 : ℝ)|^4309 ≤ (1522233248503/12500000000000 : ℝ)^3285
        have hw : |(-200852857/1000000000 : ℝ)|=(200852857/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080733203/2000000000 : ℝ)|^4309 ≤ (5575350652117/12500000000000 : ℝ)^3285
        have hw : |(1080733203/2000000000 : ℝ)|=(1080733203/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_box_10 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2637705273/5000000000 : ℝ)*x 0 + (270183303/500000000 : ℝ)*x 1 + (-20085287/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637705273/5000000000 : ℝ)^4309 ≤ (5402415907223/12500000000000 : ℝ)^3285 := by
    have hnat : (2637705273 : ℕ)^4309*12500000000000^3285 ≤ 5402415907223^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637705273 5000000000 5402415907223 12500000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270183303/500000000 : ℝ)^4309 ≤ (22301402852079/50000000000000 : ℝ)^3285 := by
    have hnat : (270183303 : ℕ)^4309*50000000000000^3285 ≤ 22301402852079^3285*500000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270183303 500000000 22301402852079 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20085287/100000000 : ℝ)^4309 ≤ (6088933510961/50000000000000 : ℝ)^3285 := by
    have hnat : (20085287 : ℕ)^4309*50000000000000^3285 ≤ 6088933510961^3285*100000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20085287 100000000 6088933510961 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637705273/5000000000 : ℝ), (270183303/500000000 : ℝ), (-20085287/100000000 : ℝ)] ![(5402415907223/12500000000000 : ℝ), (22301402852079/50000000000000 : ℝ), (6088933510961/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637705273/5000000000 : ℝ)|^4309 ≤ (5402415907223/12500000000000 : ℝ)^3285
        have hw : |(2637705273/5000000000 : ℝ)|=(2637705273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270183303/500000000 : ℝ)|^4309 ≤ (22301402852079/50000000000000 : ℝ)^3285
        have hw : |(270183303/500000000 : ℝ)|=(270183303/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-20085287/100000000 : ℝ)|^4309 ≤ (6088933510961/50000000000000 : ℝ)^3285
        have hw : |(-20085287/100000000 : ℝ)|=(20085287/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_box_11 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2252841727/5000000000 : ℝ)*x 0 + (423793681/1000000000 : ℝ)*x 1 + (4237937169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2252841727/5000000000 : ℝ)^4309 ≤ (35142364303151/100000000000000 : ℝ)^3285 := by
    have hnat : (2252841727 : ℕ)^4309*100000000000000^3285 ≤ 35142364303151^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252841727 5000000000 35142364303151 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (423793681/1000000000 : ℝ)^4309 ≤ (32428816039087/100000000000000 : ℝ)^3285 := by
    have hnat : (423793681 : ℕ)^4309*100000000000000^3285 ≤ 32428816039087^3285*1000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423793681 1000000000 32428816039087 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4237937169/10000000000 : ℝ)^4309 ≤ (8107204910621/25000000000000 : ℝ)^3285 := by
    have hnat : (4237937169 : ℕ)^4309*25000000000000^3285 ≤ 8107204910621^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237937169 10000000000 8107204910621 25000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2252841727/5000000000 : ℝ), (423793681/1000000000 : ℝ), (4237937169/10000000000 : ℝ)] ![(35142364303151/100000000000000 : ℝ), (32428816039087/100000000000000 : ℝ), (8107204910621/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2252841727/5000000000 : ℝ)|^4309 ≤ (35142364303151/100000000000000 : ℝ)^3285
        have hw : |(2252841727/5000000000 : ℝ)|=(2252841727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(423793681/1000000000 : ℝ)|^4309 ≤ (32428816039087/100000000000000 : ℝ)^3285
        have hw : |(423793681/1000000000 : ℝ)|=(423793681/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4237937169/10000000000 : ℝ)|^4309 ≤ (8107204910621/25000000000000 : ℝ)^3285
        have hw : |(4237937169/10000000000 : ℝ)|=(4237937169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_box_12 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1942171803/10000000000 : ℝ)*x 0 + (2736625209/5000000000 : ℝ)*x 1 + (5254003127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1942171803/10000000000 : ℝ)^4309 ≤ (11652864930529/100000000000000 : ℝ)^3285 := by
    have hnat : (1942171803 : ℕ)^4309*100000000000000^3285 ≤ 11652864930529^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1942171803 10000000000 11652864930529 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2736625209/5000000000 : ℝ)^4309 ≤ (45357714770409/100000000000000 : ℝ)^3285 := by
    have hnat : (2736625209 : ℕ)^4309*100000000000000^3285 ≤ 45357714770409^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2736625209 5000000000 45357714770409 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254003127/10000000000 : ℝ)^4309 ≤ (8597884056717/20000000000000 : ℝ)^3285 := by
    have hnat : (5254003127 : ℕ)^4309*20000000000000^3285 ≤ 8597884056717^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254003127 10000000000 8597884056717 20000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1942171803/10000000000 : ℝ), (2736625209/5000000000 : ℝ), (5254003127/10000000000 : ℝ)] ![(11652864930529/100000000000000 : ℝ), (45357714770409/100000000000000 : ℝ), (8597884056717/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1942171803/10000000000 : ℝ)|^4309 ≤ (11652864930529/100000000000000 : ℝ)^3285
        have hw : |(-1942171803/10000000000 : ℝ)|=(1942171803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2736625209/5000000000 : ℝ)|^4309 ≤ (45357714770409/100000000000000 : ℝ)^3285
        have hw : |(2736625209/5000000000 : ℝ)|=(2736625209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254003127/10000000000 : ℝ)|^4309 ≤ (8597884056717/20000000000000 : ℝ)^3285
        have hw : |(5254003127/10000000000 : ℝ)|=(5254003127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_box_13 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2690251187/5000000000 : ℝ)*x 0 + (-1034335789/5000000000 : ℝ)*x 1 + (105080061/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2690251187/5000000000 : ℝ)^4309 ≤ (44352176357409/100000000000000 : ℝ)^3285 := by
    have hnat : (2690251187 : ℕ)^4309*100000000000000^3285 ≤ 44352176357409^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690251187 5000000000 44352176357409 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1034335789/5000000000 : ℝ)^4309 ≤ (632920209011/5000000000000 : ℝ)^3285 := by
    have hnat : (1034335789 : ℕ)^4309*5000000000000^3285 ≤ 632920209011^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034335789 5000000000 632920209011 5000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105080061/200000000 : ℝ)^4309 ≤ (1074735486429/2500000000000 : ℝ)^3285 := by
    have hnat : (105080061 : ℕ)^4309*2500000000000^3285 ≤ 1074735486429^3285*200000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105080061 200000000 1074735486429 2500000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2690251187/5000000000 : ℝ), (-1034335789/5000000000 : ℝ), (105080061/200000000 : ℝ)] ![(44352176357409/100000000000000 : ℝ), (632920209011/5000000000000 : ℝ), (1074735486429/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2690251187/5000000000 : ℝ)|^4309 ≤ (44352176357409/100000000000000 : ℝ)^3285
        have hw : |(2690251187/5000000000 : ℝ)|=(2690251187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1034335789/5000000000 : ℝ)|^4309 ≤ (632920209011/5000000000000 : ℝ)^3285
        have hw : |(-1034335789/5000000000 : ℝ)|=(1034335789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105080061/200000000 : ℝ)|^4309 ≤ (1074735486429/2500000000000 : ℝ)^3285
        have hw : |(105080061/200000000 : ℝ)|=(105080061/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_box_14 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5380502171/10000000000 : ℝ)*x 0 + (5254003531/10000000000 : ℝ)*x 1 + (-258583901/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380502171/10000000000 : ℝ)^4309 ≤ (11088043540609/25000000000000 : ℝ)^3285 := by
    have hnat : (5380502171 : ℕ)^4309*25000000000000^3285 ≤ 11088043540609^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380502171 10000000000 11088043540609 25000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5254003531/10000000000 : ℝ)^4309 ≤ (42989424619629/100000000000000 : ℝ)^3285 := by
    have hnat : (5254003531 : ℕ)^4309*100000000000000^3285 ≤ 42989424619629^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254003531 10000000000 42989424619629 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258583901/1250000000 : ℝ)^4309 ≤ (12658401210399/100000000000000 : ℝ)^3285 := by
    have hnat : (258583901 : ℕ)^4309*100000000000000^3285 ≤ 12658401210399^3285*1250000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258583901 1250000000 12658401210399 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380502171/10000000000 : ℝ), (5254003531/10000000000 : ℝ), (-258583901/1250000000 : ℝ)] ![(11088043540609/25000000000000 : ℝ), (42989424619629/100000000000000 : ℝ), (12658401210399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380502171/10000000000 : ℝ)|^4309 ≤ (11088043540609/25000000000000 : ℝ)^3285
        have hw : |(5380502171/10000000000 : ℝ)|=(5380502171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5254003531/10000000000 : ℝ)|^4309 ≤ (42989424619629/100000000000000 : ℝ)^3285
        have hw : |(5254003531/10000000000 : ℝ)|=(5254003531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-258583901/1250000000 : ℝ)|^4309 ≤ (12658401210399/100000000000000 : ℝ)^3285
        have hw : |(-258583901/1250000000 : ℝ)|=(258583901/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_box_15 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4148976967/10000000000 : ℝ)*x 0 + (4416285257/10000000000 : ℝ)*x 1 + (552035573/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4148976967/10000000000 : ℝ)^4309 ≤ (3153883325759/10000000000000 : ℝ)^3285 := by
    have hnat : (4148976967 : ℕ)^4309*10000000000000^3285 ≤ 3153883325759^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4148976967 10000000000 3153883325759 10000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4416285257/10000000000 : ℝ)^4309 ≤ (4278823347969/12500000000000 : ℝ)^3285 := by
    have hnat : (4416285257 : ℕ)^4309*12500000000000^3285 ≤ 4278823347969^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4416285257 10000000000 4278823347969 12500000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (552035573/1250000000 : ℝ)^4309 ≤ (17115289970637/50000000000000 : ℝ)^3285 := by
    have hnat : (552035573 : ℕ)^4309*50000000000000^3285 ≤ 17115289970637^3285*1250000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552035573 1250000000 17115289970637 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4148976967/10000000000 : ℝ), (4416285257/10000000000 : ℝ), (552035573/1250000000 : ℝ)] ![(3153883325759/10000000000000 : ℝ), (4278823347969/12500000000000 : ℝ), (17115289970637/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4148976967/10000000000 : ℝ)|^4309 ≤ (3153883325759/10000000000000 : ℝ)^3285
        have hw : |(4148976967/10000000000 : ℝ)|=(4148976967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4416285257/10000000000 : ℝ)|^4309 ≤ (4278823347969/12500000000000 : ℝ)^3285
        have hw : |(4416285257/10000000000 : ℝ)|=(4416285257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(552035573/1250000000 : ℝ)|^4309 ≤ (17115289970637/50000000000000 : ℝ)^3285
        have hw : |(552035573/1250000000 : ℝ)|=(552035573/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1349_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4843891/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14711/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5583/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31429/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11791/20000 : ℝ) ∧ (15999/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84379/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14711/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5583/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14711/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5583/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14711/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5583/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14711/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5583/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14711/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5583/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14711/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5583/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5583/50000 : ℝ) ^ (1077/256 : ℝ) ≤ (9873600451412033/100000000000000000000 : ℝ) := by
    have hpowers : (5583/50000 : ℝ)^1077 ≤ (9873600451412033/100000000000000000000 : ℝ)^256 := by
      have hnat : (5583 : ℕ)^1077*100000000000000000000^256 ≤ 9873600451412033^256*50000^1077 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5583 50000 9873600451412033 100000000000000000000 1077 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5583/50000 : ℝ)) (X := (9873600451412033/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14711/100000 : ℝ) ^ (1077/256 : ℝ) ≤ (6299044854108527/20000000000000000000 : ℝ) := by
    have hpowers : (14711/100000 : ℝ)^1077 ≤ (6299044854108527/20000000000000000000 : ℝ)^256 := by
      have hnat : (14711 : ℕ)^1077*20000000000000000000^256 ≤ 6299044854108527^256*100000^1077 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14711 100000 6299044854108527 20000000000000000000 1077 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14711/100000 : ℝ)) (X := (6299044854108527/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009873600451412033/50000000000000000000 : ℝ) ≤ (500023467516159/500000000000000 : ℝ) ^ (1077/256 : ℝ) := by
    have hpowers : (50009873600451412033/50000000000000000000 : ℝ)^256 ≤ (500023467516159/500000000000000 : ℝ)^1077 := by
      have hnat : (50009873600451412033 : ℕ)^256*500000000000000^1077 ≤ 500023467516159^1077*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009873600451412033 50000000000000000000 500023467516159 500000000000000 256 1077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500023467516159/500000000000000 : ℝ)) (X := (50009873600451412033/50000000000000000000 : ℝ)) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (25010342206180488667/25000000000000000000 : ℝ) ≤ (10000983170813387/10000000000000000 : ℝ) ^ (1077/256 : ℝ) := by
    have hpowers : (25010342206180488667/25000000000000000000 : ℝ)^256 ≤ (10000983170813387/10000000000000000 : ℝ)^1077 := by
      have hnat : (25010342206180488667 : ℕ)^256*10000000000000000^1077 ≤ 10000983170813387^1077*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010342206180488667 25000000000000000000 10000983170813387 10000000000000000 256 1077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000983170813387/10000000000000000 : ℝ)) (X := (25010342206180488667/25000000000000000000 : ℝ)) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006299044854108527/10000000000000000000 : ℝ) ≤ (5000748495651797/5000000000000000 : ℝ) ^ (1077/256 : ℝ) := by
    have hpowers : (10006299044854108527/10000000000000000000 : ℝ)^256 ≤ (5000748495651797/5000000000000000 : ℝ)^1077 := by
      have hnat : (10006299044854108527 : ℕ)^256*5000000000000000^1077 ≤ 5000748495651797^1077*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006299044854108527 10000000000000000000 5000748495651797 5000000000000000 256 1077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000748495651797/5000000000000000 : ℝ)) (X := (10006299044854108527/10000000000000000000 : ℝ)) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9873600451412033/100000000000000000000 : ℝ) ≤ ((4430023650963546297/4431250000000000000 : ℝ)+2*(513820490207/354500000000000 : ℝ)*(5583/50000 : ℝ))^(1077/256 : ℝ) := by
    rw [show (4430023650963546297/4431250000000000000 : ℝ)+2*(513820490207/354500000000000 : ℝ)*(5583/50000 : ℝ)=(500023467516159/500000000000000 : ℝ) by norm_num, show 1+2*(9873600451412033/100000000000000000000 : ℝ)=(50009873600451412033/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6299044854108527/20000000000000000000 : ℝ)+(9873600451412033/100000000000000000000 : ℝ) ≤ ((4430023650963546297/4431250000000000000 : ℝ)+(513820490207/354500000000000 : ℝ)*((14711/100000 : ℝ)+(5583/50000 : ℝ)))^(1077/256 : ℝ) := by
    rw [show (4430023650963546297/4431250000000000000 : ℝ)+(513820490207/354500000000000 : ℝ)*((14711/100000 : ℝ)+(5583/50000 : ℝ))=(10000983170813387/10000000000000000 : ℝ) by norm_num, show 1+(6299044854108527/20000000000000000000 : ℝ)+(9873600451412033/100000000000000000000 : ℝ)=(25010342206180488667/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6299044854108527/20000000000000000000 : ℝ) ≤ ((4430023650963546297/4431250000000000000 : ℝ)+2*(513820490207/354500000000000 : ℝ)*(14711/100000 : ℝ))^(1077/256 : ℝ) := by
    rw [show (4430023650963546297/4431250000000000000 : ℝ)+2*(513820490207/354500000000000 : ℝ)*(14711/100000 : ℝ)=(5000748495651797/5000000000000000 : ℝ) by norm_num, show 1+2*(6299044854108527/20000000000000000000 : ℝ)=(10006299044854108527/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4430023650963546297/4431250000000000000 : ℝ)*(X 1 0+X 2 0)+(513820490207/354500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1077/256 : ℝ)) (lo := (5583/50000 : ℝ)) (hi := (14711/100000 : ℝ)) (c := (4430023650963546297/4431250000000000000 : ℝ)) (alpha := (513820490207/354500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4430023650963546297/4431250000000000000 : ℝ)*(X 0 1+X 2 1)+(513820490207/354500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1077/256 : ℝ)) (lo := (5583/50000 : ℝ)) (hi := (14711/100000 : ℝ)) (c := (4430023650963546297/4431250000000000000 : ℝ)) (alpha := (513820490207/354500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4430023650963546297/4431250000000000000 : ℝ)*(X 0 2+X 1 2)+(513820490207/354500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1077/256 : ℝ)) (lo := (5583/50000 : ℝ)) (hi := (14711/100000 : ℝ)) (c := (4430023650963546297/4431250000000000000 : ℝ)) (alpha := (513820490207/354500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-93561837/500000000 : ℝ)*X 0 0+(5389649051/10000000000 : ℝ)*X 0 1+(5389648907/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((660657287/1250000000 : ℝ)*X 1 0+(-1007145417/5000000000 : ℝ)*X 1 1+(5389648811/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5285258169/10000000000 : ℝ)*X 2 0+(2694824501/5000000000 : ℝ)*X 2 1+(-1007145373/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((27955149/62500000 : ℝ)*X 0 0+(4254654159/10000000000 : ℝ)*X 0 1+(1063663577/2500000000 : ℝ)*X 0 2+(27955149/62500000 : ℝ)*X 1 0+(4254654159/10000000000 : ℝ)*X 1 1+(1063663577/2500000000 : ℝ)*X 1 2+(27955149/62500000 : ℝ)*X 2 0+(4254654159/10000000000 : ℝ)*X 2 1+(1063663577/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2207395451/10000000000 : ℝ)*X 0 0+(2632539243/5000000000 : ℝ)*X 0 1+(2632539311/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2686364039/5000000000 : ℝ)*X 1 0+(-1032163003/5000000000 : ℝ)*X 1 1+(2632539299/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5372728303/10000000000 : ℝ)*X 2 0+(2632539231/5000000000 : ℝ)*X 2 1+(-412865177/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2087915001/5000000000 : ℝ)*X 0 0+(88061959/200000000 : ℝ)*X 0 1+(440309763/1000000000 : ℝ)*X 0 2+(2087915001/5000000000 : ℝ)*X 1 0+(88061959/200000000 : ℝ)*X 1 1+(440309763/1000000000 : ℝ)*X 1 2+(2087915001/5000000000 : ℝ)*X 2 0+(88061959/200000000 : ℝ)*X 2 1+(440309763/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2136784113/10000000000 : ℝ)*X 0 0+(1294821847/2500000000 : ℝ)*X 0 1+(168864569/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((20607073/39062500 : ℝ)*X 1 0+(-200852857/1000000000 : ℝ)*X 1 1+(1080733203/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2637705273/5000000000 : ℝ)*X 2 0+(270183303/500000000 : ℝ)*X 2 1+(-20085287/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2252841727/5000000000 : ℝ)*X 0 0+(423793681/1000000000 : ℝ)*X 0 1+(4237937169/10000000000 : ℝ)*X 0 2+(2252841727/5000000000 : ℝ)*X 1 0+(423793681/1000000000 : ℝ)*X 1 1+(4237937169/10000000000 : ℝ)*X 1 2+(2252841727/5000000000 : ℝ)*X 2 0+(423793681/1000000000 : ℝ)*X 2 1+(4237937169/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1942171803/10000000000 : ℝ)*X 0 0+(2736625209/5000000000 : ℝ)*X 0 1+(5254003127/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2690251187/5000000000 : ℝ)*X 1 0+(-1034335789/5000000000 : ℝ)*X 1 1+(105080061/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5380502171/10000000000 : ℝ)*X 2 0+(5254003531/10000000000 : ℝ)*X 2 1+(-258583901/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4148976967/10000000000 : ℝ)*X 0 0+(4416285257/10000000000 : ℝ)*X 0 1+(552035573/1250000000 : ℝ)*X 0 2+(4148976967/10000000000 : ℝ)*X 1 0+(4416285257/10000000000 : ℝ)*X 1 1+(552035573/1250000000 : ℝ)*X 1 2+(4148976967/10000000000 : ℝ)*X 2 0+(4416285257/10000000000 : ℝ)*X 2 1+(552035573/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31429/50000 : ℝ) ≤ (-34816134805793649862044575515161/55390625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2752137/20000000000000 : ℝ)*(upper1) + (60830523/100000000000000 : ℝ)*(lower2) + (15824641/50000000000000 : ℝ)*(upper4) + (366050904715077/12500000000000 : ℝ)*(major0) + (366050904715077/12500000000000 : ℝ)*(major1) + (366050904715077/12500000000000 : ℝ)*(major2) + (269705749/50000000000000 : ℝ)*(sp1) + (113196269/50000000000000 : ℝ)*(sp2) + (478948901/100000000000000 : ℝ)*(sp3) + (498565696656529/12500000000000 : ℝ)*(sp4) + (398852582090131/10000000000000 : ℝ)*(sp5) + (398852613392027/10000000000000 : ℝ)*(sp6) + (944619758981019/50000000000000 : ℝ)*(sp7) + (24595643/3125000000000 : ℝ)*(sp8) + (1889239996910939/100000000000000 : ℝ)*(f.failure) + (498565795039101/12500000000000 : ℝ)*(f.sum) + (33174860504147/4431250000000000000000000000 : ℝ)*base66 + (19558016003398997/27695312500000000000000000000000 : ℝ)*base67 + (301937226926717631/55390625000000000000000000000000 : ℝ)*base70 + (259206015387342631/55390625000000000000000000000000 : ℝ)*base72 + (4395894602563/17725000000000000000000000000 : ℝ)*base74 + (151794963763748881/55390625000000000000000000000000 : ℝ)*base76 + (346350708910467631/55390625000000000000000000000000 : ℝ)*base78 + (45295946339961497/27695312500000000000000000000000 : ℝ)*base79 + (4321127413119/8862500000000000000000000000 : ℝ)*base82 + (223649/312500000000000000000 : ℝ)*base89 + (223649/312500000000000000000 : ℝ)*base91 + (223649/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (11791/20000 : ℝ) ≤ (65313566286211055268421123118649/110781250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16592409/100000000000000 : ℝ)*(upper0) + (2975089/20000000000000 : ℝ)*(lower1) + (5308829/100000000000000 : ℝ)*(upper4) + (1498666681967811/50000000000000 : ℝ)*(major0) + (1498666681967811/50000000000000 : ℝ)*(major1) + (1498666681967811/50000000000000 : ℝ)*(major2) + (1010326449888467/25000000000000 : ℝ)*(sp0) + (2020633754729909/50000000000000 : ℝ)*(sp1) + (202065256570637/5000000000000 : ℝ)*(sp2) + (386740935596339/20000000000000 : ℝ)*(sp3) + (503114979/25000000000000 : ℝ)*(sp6) + (62325749/2500000000000 : ℝ)*(sp7) + (1344318787/100000000000000 : ℝ)*(sp8) + (39634412837/100000000000000 : ℝ)*(sp9) + (241713396376457/12500000000000 : ℝ)*(f.failure) + (252581696492041/6250000000000 : ℝ)*(f.sum) + (2471235065729/17725000000000000000000000000 : ℝ)*base65 + (1565773806779145867/221562500000000000000000000000000 : ℝ)*base67 + (406779339916791633/221562500000000000000000000000000 : ℝ)*base70 + (581021201568208367/221562500000000000000000000000000 : ℝ)*base71 + (507784171855579/17725000000000000000000000000 : ℝ)*base73 + (1084925867105395867/221562500000000000000000000000000 : ℝ)*base75 + (1072837313874291633/221562500000000000000000000000000 : ℝ)*base78 + (9871957610831645867/221562500000000000000000000000000 : ℝ)*base79 + (41055453146377/8862500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (330437/39062500000000000000 : ℝ)*base89 + (330437/39062500000000000000 : ℝ)*base91 + (330437/39062500000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (15999/20000 : ℝ) ≤ (177244941560981235368723604593487/221562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5036411/5000000000000 : ℝ)*(upper2) + (20730489/25000000000000 : ℝ)*(lower3) + (9856297/100000000000000 : ℝ)*(lower4) + (9135581/25000000000000 : ℝ)*(lower5) + (1654571728058439/50000000000000 : ℝ)*(major0) + (1654571728058439/50000000000000 : ℝ)*(major1) + (3309143456116879/100000000000000 : ℝ)*(major2) + (48030592227/100000000000000 : ℝ)*(sp1) + (2647176991/6250000000000 : ℝ)*(sp3) + (1016235547/20000000000000 : ℝ)*(sp4) + (2228373404377459/50000000000000 : ℝ)*(sp8) + (2228351929670213/50000000000000 : ℝ)*(sp9) + (1114187972483163/25000000000000 : ℝ)*(sp10) + (1067413380913857/50000000000000 : ℝ)*(sp11) + (2134869116659571/100000000000000 : ℝ)*(f.failure) + (1114187972483163/25000000000000 : ℝ)*(f.sum) + (644840478633049/35450000000000000000000000000 : ℝ)*base65 + (1476844728871618367/221562500000000000000000000000000 : ℝ)*base68 + (3917294159351027937/443125000000000000000000000000000 : ℝ)*base70 + (1822239537728493367/221562500000000000000000000000000 : ℝ)*base72 + (216677742119999/35450000000000000000000000000 : ℝ)*base73 + (410811635886652937/443125000000000000000000000000000 : ℝ)*base76 + (8788542807392712883/221562500000000000000000000000000 : ℝ)*base77 + (688437162477287117/221562500000000000000000000000000 : ℝ)*base80 + (2379556273363/2215625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (2280761/312500000000000000000 : ℝ)*base89 + (2280761/312500000000000000000 : ℝ)*base91 + (844239/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-84379/100000 : ℝ) ≤ (-186947501125386456357105902786109/221562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10129891/5000000000000 : ℝ)*(lower0) + (65415117/100000000000000 : ℝ)*(upper1) + (40253011/25000000000000 : ℝ)*(upper3) + (400766883/100000000000000 : ℝ)*(upper5) + (3345677380705119/100000000000000 : ℝ)*(major0) + (3345677380705119/100000000000000 : ℝ)*(major1) + (20910483629407/625000000000 : ℝ)*(major2) + (1073500419/100000000000000 : ℝ)*(sp4) + (119096502333/100000000000000 : ℝ)*(sp5) + (7452806109/50000000000000 : ℝ)*(sp7) + (2280520303268933/50000000000000 : ℝ)*(sp12) + (285057661470997/6250000000000 : ℝ)*(sp13) + (912208336007657/20000000000000 : ℝ)*(sp14) + (2158423798872151/100000000000000 : ℝ)*(sp15) + (215843870448437/10000000000000 : ℝ)*(f.failure) + (912208336007657/20000000000000 : ℝ)*(f.sum) + (132438640180773/35450000000000000000000000000 : ℝ)*base65 + (5920067183253730657/443125000000000000000000000000000 : ℝ)*base68 + (116850809228857343/22156250000000000000000000000000 : ℝ)*base70 + (1264574591925019343/443125000000000000000000000000000 : ℝ)*base71 + (191222077819377/35450000000000000000000000000 : ℝ)*base74 + (124276988979044843/22156250000000000000000000000000 : ℝ)*base76 + (968498432349306843/443125000000000000000000000000000 : ℝ)*base77 + (1961591163420556843/443125000000000000000000000000000 : ℝ)*base79 + (93061432819733/17725000000000000000000000000 : ℝ)*base81 + (260867/31250000000000000000 : ℝ)*base89 + (260867/31250000000000000000 : ℝ)*base91 + (51633/31250000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1349_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4843891/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14711/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5583/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31429/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(11791/20000 : ℝ) else (15999/20000 : ℝ) ≤ X j i ∧ X j i ≤ (84379/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1349_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1349_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4843891/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14719/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5579/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31429/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(11791/20000 : ℝ) else (15999/20000 : ℝ) ≤ X j i ∧ X j i ≤ (84379/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1349_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1349_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1349_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4843891/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14719/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5579/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31429/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(11791/20000 : ℝ) else (15999/20000 : ℝ) ≤ X j i ∧ X j i ≤ (84379/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1349_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

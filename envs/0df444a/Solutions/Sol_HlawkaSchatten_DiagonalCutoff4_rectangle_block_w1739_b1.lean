-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1739_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:13:06.421279+00:00
-- url     : https://prove2.me/submissions/5528887a-d3c1-4df3-bbb7-21c7db510671

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
theorem support_rectangle_w1739_s3_0 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-643188787/5000000000 : ℝ)*x 0 + (1378080061/2500000000 : ℝ)*x 1 + (5077464321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (643188787/5000000000 : ℝ)^5599 ≤ (8128730667849/100000000000000 : ℝ)^4575 := by
    have hnat : (643188787 : ℕ)^5599*100000000000000^4575 ≤ 8128730667849^4575*5000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643188787 5000000000 8128730667849 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1378080061/2500000000 : ℝ)^5599 ≤ (48243475391251/100000000000000 : ℝ)^4575 := by
    have hnat : (1378080061 : ℕ)^5599*100000000000000^4575 ≤ 48243475391251^4575*2500000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378080061 2500000000 48243475391251 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5077464321/10000000000 : ℝ)^5599 ≤ (21813896963499/50000000000000 : ℝ)^4575 := by
    have hnat : (5077464321 : ℕ)^5599*50000000000000^4575 ≤ 21813896963499^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5077464321 10000000000 21813896963499 50000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-643188787/5000000000 : ℝ), (1378080061/2500000000 : ℝ), (5077464321/10000000000 : ℝ)] ![(8128730667849/100000000000000 : ℝ), (48243475391251/100000000000000 : ℝ), (21813896963499/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-643188787/5000000000 : ℝ)|^5599 ≤ (8128730667849/100000000000000 : ℝ)^4575
        have hw : |(-643188787/5000000000 : ℝ)|=(643188787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1378080061/2500000000 : ℝ)|^5599 ≤ (48243475391251/100000000000000 : ℝ)^4575
        have hw : |(1378080061/2500000000 : ℝ)|=(1378080061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5077464321/10000000000 : ℝ)|^5599 ≤ (21813896963499/50000000000000 : ℝ)^4575
        have hw : |(5077464321/10000000000 : ℝ)|=(5077464321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_s3_1 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344038737/10000000000 : ℝ)*x 0 + (-1514317269/10000000000 : ℝ)*x 1 + (2538732097/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344038737/10000000000 : ℝ)^5599 ≤ (5805905811137/12500000000000 : ℝ)^4575 := by
    have hnat : (5344038737 : ℕ)^5599*12500000000000^4575 ≤ 5805905811137^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344038737 10000000000 5805905811137 12500000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1514317269/10000000000 : ℝ)^5599 ≤ (9924960912283/100000000000000 : ℝ)^4575 := by
    have hnat : (1514317269 : ℕ)^5599*100000000000000^4575 ≤ 9924960912283^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1514317269 10000000000 9924960912283 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2538732097/5000000000 : ℝ)^5599 ≤ (43627792591511/100000000000000 : ℝ)^4575 := by
    have hnat : (2538732097 : ℕ)^5599*100000000000000^4575 ≤ 43627792591511^4575*5000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2538732097 5000000000 43627792591511 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344038737/10000000000 : ℝ), (-1514317269/10000000000 : ℝ), (2538732097/5000000000 : ℝ)] ![(5805905811137/12500000000000 : ℝ), (9924960912283/100000000000000 : ℝ), (43627792591511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344038737/10000000000 : ℝ)|^5599 ≤ (5805905811137/12500000000000 : ℝ)^4575
        have hw : |(5344038737/10000000000 : ℝ)|=(5344038737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1514317269/10000000000 : ℝ)|^5599 ≤ (9924960912283/100000000000000 : ℝ)^4575
        have hw : |(-1514317269/10000000000 : ℝ)|=(1514317269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2538732097/5000000000 : ℝ)|^5599 ≤ (43627792591511/100000000000000 : ℝ)^4575
        have hw : |(2538732097/5000000000 : ℝ)|=(2538732097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_s3_2 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668004857/1250000000 : ℝ)*x 0 + (2538732051/5000000000 : ℝ)*x 1 + (-94644827/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668004857/1250000000 : ℝ)^5599 ≤ (5805905969359/12500000000000 : ℝ)^4575 := by
    have hnat : (668004857 : ℕ)^5599*12500000000000^4575 ≤ 5805905969359^4575*1250000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668004857 1250000000 5805905969359 12500000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2538732051/5000000000 : ℝ)^5599 ≤ (5453473953009/12500000000000 : ℝ)^4575 := by
    have hnat : (2538732051 : ℕ)^5599*12500000000000^4575 ≤ 5453473953009^4575*5000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2538732051 5000000000 5453473953009 12500000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (94644827/625000000 : ℝ)^5599 ≤ (620310038469/6250000000000 : ℝ)^4575 := by
    have hnat : (94644827 : ℕ)^5599*6250000000000^4575 ≤ 620310038469^4575*625000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94644827 625000000 620310038469 6250000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668004857/1250000000 : ℝ), (2538732051/5000000000 : ℝ), (-94644827/625000000 : ℝ)] ![(5805905969359/12500000000000 : ℝ), (5453473953009/12500000000000 : ℝ), (620310038469/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668004857/1250000000 : ℝ)|^5599 ≤ (5805905969359/12500000000000 : ℝ)^4575
        have hw : |(668004857/1250000000 : ℝ)|=(668004857/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2538732051/5000000000 : ℝ)|^5599 ≤ (5453473953009/12500000000000 : ℝ)^4575
        have hw : |(2538732051/5000000000 : ℝ)|=(2538732051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-94644827/625000000 : ℝ)|^5599 ≤ (620310038469/6250000000000 : ℝ)^4575
        have hw : |(-94644827/625000000 : ℝ)|=(94644827/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_s3_3 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1011139937/2500000000 : ℝ)*x 0 + (1697584557/5000000000 : ℝ)*x 1 + (4759929141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1011139937/2500000000 : ℝ)^5599 ≤ (6605552613463/20000000000000 : ℝ)^4575 := by
    have hnat : (1011139937 : ℕ)^5599*20000000000000^4575 ≤ 6605552613463^4575*2500000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011139937 2500000000 6605552613463 20000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1697584557/5000000000 : ℝ)^5599 ≤ (26659770272241/100000000000000 : ℝ)^4575 := by
    have hnat : (1697584557 : ℕ)^5599*100000000000000^4575 ≤ 26659770272241^4575*5000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1697584557 5000000000 26659770272241 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4759929141/10000000000 : ℝ)^5599 ≤ (1259764582867/3125000000000 : ℝ)^4575 := by
    have hnat : (4759929141 : ℕ)^5599*3125000000000^4575 ≤ 1259764582867^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4759929141 10000000000 1259764582867 3125000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1011139937/2500000000 : ℝ), (1697584557/5000000000 : ℝ), (4759929141/10000000000 : ℝ)] ![(6605552613463/20000000000000 : ℝ), (26659770272241/100000000000000 : ℝ), (1259764582867/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1011139937/2500000000 : ℝ)|^5599 ≤ (6605552613463/20000000000000 : ℝ)^4575
        have hw : |(1011139937/2500000000 : ℝ)|=(1011139937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1697584557/5000000000 : ℝ)|^5599 ≤ (26659770272241/100000000000000 : ℝ)^4575
        have hw : |(1697584557/5000000000 : ℝ)|=(1697584557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4759929141/10000000000 : ℝ)|^5599 ≤ (1259764582867/3125000000000 : ℝ)^4575
        have hw : |(4759929141/10000000000 : ℝ)|=(4759929141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_s3_4 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1286752853/10000000000 : ℝ)*x 0 + (1271102457/2500000000 : ℝ)*x 1 + (5505228281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1286752853/10000000000 : ℝ)^5599 ≤ (813163296639/10000000000000 : ℝ)^4575 := by
    have hnat : (1286752853 : ℕ)^5599*10000000000000^4575 ≤ 813163296639^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1286752853 10000000000 813163296639 10000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1271102457/2500000000 : ℝ)^5599 ≤ (43700841560547/100000000000000 : ℝ)^4575 := by
    have hnat : (1271102457 : ℕ)^5599*100000000000000^4575 ≤ 43700841560547^4575*2500000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1271102457 2500000000 43700841560547 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5505228281/10000000000 : ℝ)^5599 ≤ (24083762726971/50000000000000 : ℝ)^4575 := by
    have hnat : (5505228281 : ℕ)^5599*50000000000000^4575 ≤ 24083762726971^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5505228281 10000000000 24083762726971 50000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1286752853/10000000000 : ℝ), (1271102457/2500000000 : ℝ), (5505228281/10000000000 : ℝ)] ![(813163296639/10000000000000 : ℝ), (43700841560547/100000000000000 : ℝ), (24083762726971/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1286752853/10000000000 : ℝ)|^5599 ≤ (813163296639/10000000000000 : ℝ)^4575
        have hw : |(-1286752853/10000000000 : ℝ)|=(1286752853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1271102457/2500000000 : ℝ)|^5599 ≤ (43700841560547/100000000000000 : ℝ)^4575
        have hw : |(1271102457/2500000000 : ℝ)|=(1271102457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5505228281/10000000000 : ℝ)|^5599 ≤ (24083762726971/50000000000000 : ℝ)^4575
        have hw : |(5505228281/10000000000 : ℝ)|=(5505228281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_s3_5 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2614239339/5000000000 : ℝ)*x 0 + (-135819127/1250000000 : ℝ)*x 1 + (688153537/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2614239339/5000000000 : ℝ)^5599 ≤ (45221052232837/100000000000000 : ℝ)^4575 := by
    have hnat : (2614239339 : ℕ)^5599*100000000000000^4575 ≤ 45221052232837^4575*5000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614239339 5000000000 45221052232837 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135819127/1250000000 : ℝ)^5599 ≤ (6611422135193/100000000000000 : ℝ)^4575 := by
    have hnat : (135819127 : ℕ)^5599*100000000000000^4575 ≤ 6611422135193^4575*1250000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135819127 1250000000 6611422135193 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (688153537/1250000000 : ℝ)^5599 ≤ (24083762807279/50000000000000 : ℝ)^4575 := by
    have hnat : (688153537 : ℕ)^5599*50000000000000^4575 ≤ 24083762807279^4575*1250000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688153537 1250000000 24083762807279 50000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2614239339/5000000000 : ℝ), (-135819127/1250000000 : ℝ), (688153537/1250000000 : ℝ)] ![(45221052232837/100000000000000 : ℝ), (6611422135193/100000000000000 : ℝ), (24083762807279/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2614239339/5000000000 : ℝ)|^5599 ≤ (45221052232837/100000000000000 : ℝ)^4575
        have hw : |(2614239339/5000000000 : ℝ)|=(2614239339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-135819127/1250000000 : ℝ)|^5599 ≤ (6611422135193/100000000000000 : ℝ)^4575
        have hw : |(-135819127/1250000000 : ℝ)|=(135819127/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(688153537/1250000000 : ℝ)|^5599 ≤ (24083762807279/50000000000000 : ℝ)^4575
        have hw : |(688153537/1250000000 : ℝ)|=(688153537/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_s3_6 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2614239309/5000000000 : ℝ)*x 0 + (2752614171/5000000000 : ℝ)*x 1 + (-217310607/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2614239309/5000000000 : ℝ)^5599 ≤ (22610525798873/50000000000000 : ℝ)^4575 := by
    have hnat : (2614239309 : ℕ)^5599*50000000000000^4575 ≤ 22610525798873^4575*5000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614239309 5000000000 22610525798873 50000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2752614171/5000000000 : ℝ)^5599 ≤ (9633505221423/20000000000000 : ℝ)^4575 := by
    have hnat : (2752614171 : ℕ)^5599*20000000000000^4575 ≤ 9633505221423^4575*5000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2752614171 5000000000 9633505221423 20000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217310607/2000000000 : ℝ)^5599 ≤ (165285556917/2500000000000 : ℝ)^4575 := by
    have hnat : (217310607 : ℕ)^5599*2500000000000^4575 ≤ 165285556917^4575*2000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217310607 2000000000 165285556917 2500000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2614239309/5000000000 : ℝ), (2752614171/5000000000 : ℝ), (-217310607/2000000000 : ℝ)] ![(22610525798873/50000000000000 : ℝ), (9633505221423/20000000000000 : ℝ), (165285556917/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2614239309/5000000000 : ℝ)|^5599 ≤ (22610525798873/50000000000000 : ℝ)^4575
        have hw : |(2614239309/5000000000 : ℝ)|=(2614239309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2752614171/5000000000 : ℝ)|^5599 ≤ (9633505221423/20000000000000 : ℝ)^4575
        have hw : |(2752614171/5000000000 : ℝ)|=(2752614171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-217310607/2000000000 : ℝ)|^5599 ≤ (165285556917/2500000000000 : ℝ)^4575
        have hw : |(-217310607/2000000000 : ℝ)|=(217310607/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_s3_7 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4045737351/10000000000 : ℝ)*x 0 + (1184532729/2500000000 : ℝ)*x 1 + (341742673/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4045737351/10000000000 : ℝ)^5599 ≤ (1032485377751/3125000000000 : ℝ)^4575 := by
    have hnat : (4045737351 : ℕ)^5599*3125000000000^4575 ≤ 1032485377751^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4045737351 10000000000 1032485377751 3125000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1184532729/2500000000 : ℝ)^5599 ≤ (125270780403/312500000000 : ℝ)^4575 := by
    have hnat : (1184532729 : ℕ)^5599*312500000000^4575 ≤ 125270780403^4575*2500000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1184532729 2500000000 125270780403 312500000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (341742673/1000000000 : ℝ)^5599 ≤ (26873818174523/100000000000000 : ℝ)^4575 := by
    have hnat : (341742673 : ℕ)^5599*100000000000000^4575 ≤ 26873818174523^4575*1000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341742673 1000000000 26873818174523 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4045737351/10000000000 : ℝ), (1184532729/2500000000 : ℝ), (341742673/1000000000 : ℝ)] ![(1032485377751/3125000000000 : ℝ), (125270780403/312500000000 : ℝ), (26873818174523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4045737351/10000000000 : ℝ)|^5599 ≤ (1032485377751/3125000000000 : ℝ)^4575
        have hw : |(4045737351/10000000000 : ℝ)|=(4045737351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1184532729/2500000000 : ℝ)|^5599 ≤ (125270780403/312500000000 : ℝ)^4575
        have hw : |(1184532729/2500000000 : ℝ)|=(1184532729/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(341742673/1000000000 : ℝ)|^5599 ≤ (26873818174523/100000000000000 : ℝ)^4575
        have hw : |(341742673/1000000000 : ℝ)|=(341742673/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1739_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (25865111/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9097/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4441/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2221/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18191/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9097/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4441/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9097/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4441/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9097/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4441/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9097/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4441/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9097/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4441/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9097/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4441/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4441/50000 : ℝ) ^ (5583/1024 : ℝ) ≤ (92489969366963/50000000000000000000 : ℝ) := by
    have hpowers : (4441/50000 : ℝ)^5583 ≤ (92489969366963/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4441 : ℕ)^5583*50000000000000000000^1024 ≤ 92489969366963^1024*50000^5583 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4441 50000 92489969366963 50000000000000000000 5583 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4441/50000 : ℝ)) (X := (92489969366963/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5583 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9097/50000 : ℝ) ^ (5583/1024 : ℝ) ≤ (4613055119546313/50000000000000000000 : ℝ) := by
    have hpowers : (9097/50000 : ℝ)^5583 ≤ (4613055119546313/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9097 : ℕ)^5583*50000000000000000000^1024 ≤ 4613055119546313^1024*50000^5583 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9097 50000 4613055119546313 50000000000000000000 5583 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9097/50000 : ℝ)) (X := (4613055119546313/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5583 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000092489969366963/25000000000000000000 : ℝ) ≤ (10000006785569449/10000000000000000 : ℝ) ^ (5583/1024 : ℝ) := by
    have hpowers : (25000092489969366963/25000000000000000000 : ℝ)^1024 ≤ (10000006785569449/10000000000000000 : ℝ)^5583 := by
      have hnat : (25000092489969366963 : ℕ)^1024*10000000000000000^5583 ≤ 10000006785569449^5583*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000092489969366963 25000000000000000000 10000006785569449 10000000000000000 1024 5583 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000006785569449/10000000000000000 : ℝ)) (X := (25000092489969366963/25000000000000000000 : ℝ)) (by norm_num) 5583 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12501176386272228319/12500000000000000000 : ℝ) ≤ (10000172605876139/10000000000000000 : ℝ) ^ (5583/1024 : ℝ) := by
    have hpowers : (12501176386272228319/12500000000000000000 : ℝ)^1024 ≤ (10000172605876139/10000000000000000 : ℝ)^5583 := by
      have hnat : (12501176386272228319 : ℕ)^1024*10000000000000000^5583 ≤ 10000172605876139^5583*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501176386272228319 12500000000000000000 10000172605876139 10000000000000000 1024 5583 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000172605876139/10000000000000000 : ℝ)) (X := (12501176386272228319/12500000000000000000 : ℝ)) (by norm_num) 5583 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25004613055119546313/25000000000000000000 : ℝ) ≤ (10000338426182829/10000000000000000 : ℝ) ^ (5583/1024 : ℝ) := by
    have hpowers : (25004613055119546313/25000000000000000000 : ℝ)^1024 ≤ (10000338426182829/10000000000000000 : ℝ)^5583 := by
      have hnat : (25004613055119546313 : ℕ)^1024*10000000000000000^5583 ≤ 10000338426182829^5583*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004613055119546313 25000000000000000000 10000338426182829 10000000000000000 1024 5583 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000338426182829/10000000000000000 : ℝ)) (X := (25004613055119546313/25000000000000000000 : ℝ)) (by norm_num) 5583 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(92489969366963/50000000000000000000 : ℝ) ≤ ((11639639694411833491/11640000000000000000 : ℝ)+2*(16582030669/93120000000000 : ℝ)*(4441/50000 : ℝ))^(5583/1024 : ℝ) := by
    rw [show (11639639694411833491/11640000000000000000 : ℝ)+2*(16582030669/93120000000000 : ℝ)*(4441/50000 : ℝ)=(10000006785569449/10000000000000000 : ℝ) by norm_num, show 1+2*(92489969366963/50000000000000000000 : ℝ)=(25000092489969366963/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4613055119546313/50000000000000000000 : ℝ)+(92489969366963/50000000000000000000 : ℝ) ≤ ((11639639694411833491/11640000000000000000 : ℝ)+(16582030669/93120000000000 : ℝ)*((9097/50000 : ℝ)+(4441/50000 : ℝ)))^(5583/1024 : ℝ) := by
    rw [show (11639639694411833491/11640000000000000000 : ℝ)+(16582030669/93120000000000 : ℝ)*((9097/50000 : ℝ)+(4441/50000 : ℝ))=(10000172605876139/10000000000000000 : ℝ) by norm_num, show 1+(4613055119546313/50000000000000000000 : ℝ)+(92489969366963/50000000000000000000 : ℝ)=(12501176386272228319/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4613055119546313/50000000000000000000 : ℝ) ≤ ((11639639694411833491/11640000000000000000 : ℝ)+2*(16582030669/93120000000000 : ℝ)*(9097/50000 : ℝ))^(5583/1024 : ℝ) := by
    rw [show (11639639694411833491/11640000000000000000 : ℝ)+2*(16582030669/93120000000000 : ℝ)*(9097/50000 : ℝ)=(10000338426182829/10000000000000000 : ℝ) by norm_num, show 1+2*(4613055119546313/50000000000000000000 : ℝ)=(25004613055119546313/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11639639694411833491/11640000000000000000 : ℝ)*(X 1 0+X 2 0)+(16582030669/93120000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5583/1024 : ℝ)) (lo := (4441/50000 : ℝ)) (hi := (9097/50000 : ℝ)) (c := (11639639694411833491/11640000000000000000 : ℝ)) (alpha := (16582030669/93120000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11639639694411833491/11640000000000000000 : ℝ)*(X 0 1+X 2 1)+(16582030669/93120000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5583/1024 : ℝ)) (lo := (4441/50000 : ℝ)) (hi := (9097/50000 : ℝ)) (c := (11639639694411833491/11640000000000000000 : ℝ)) (alpha := (16582030669/93120000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11639639694411833491/11640000000000000000 : ℝ)*(X 0 2+X 1 2)+(16582030669/93120000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5583/1024 : ℝ)) (lo := (4441/50000 : ℝ)) (hi := (9097/50000 : ℝ)) (c := (11639639694411833491/11640000000000000000 : ℝ)) (alpha := (16582030669/93120000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-643188787/5000000000 : ℝ)*X 0 0+(1378080061/2500000000 : ℝ)*X 0 1+(5077464321/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344038737/10000000000 : ℝ)*X 1 0+(-1514317269/10000000000 : ℝ)*X 1 1+(2538732097/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668004857/1250000000 : ℝ)*X 2 0+(2538732051/5000000000 : ℝ)*X 2 1+(-94644827/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1011139937/2500000000 : ℝ)*X 0 0+(1697584557/5000000000 : ℝ)*X 0 1+(4759929141/10000000000 : ℝ)*X 0 2+(1011139937/2500000000 : ℝ)*X 1 0+(1697584557/5000000000 : ℝ)*X 1 1+(4759929141/10000000000 : ℝ)*X 1 2+(1011139937/2500000000 : ℝ)*X 2 0+(1697584557/5000000000 : ℝ)*X 2 1+(4759929141/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1286752853/10000000000 : ℝ)*X 0 0+(1271102457/2500000000 : ℝ)*X 0 1+(5505228281/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2614239339/5000000000 : ℝ)*X 1 0+(-135819127/1250000000 : ℝ)*X 1 1+(688153537/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2614239309/5000000000 : ℝ)*X 2 0+(2752614171/5000000000 : ℝ)*X 2 1+(-217310607/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4045737351/10000000000 : ℝ)*X 0 0+(1184532729/2500000000 : ℝ)*X 0 1+(341742673/1000000000 : ℝ)*X 0 2+(4045737351/10000000000 : ℝ)*X 1 0+(1184532729/2500000000 : ℝ)*X 1 1+(341742673/1000000000 : ℝ)*X 1 2+(4045737351/10000000000 : ℝ)*X 2 0+(1184532729/2500000000 : ℝ)*X 2 1+(341742673/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17065873088247206297145747/2425000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (898476341/100000000000000 : ℝ)*(base19) + (434542423/50000000000000 : ℝ)*(base23) + (8614489/20000000000000 : ℝ)*(lower2) + (154364459/100000000000000 : ℝ)*(upper3) + (120453613/100000000000000 : ℝ)*(upper5) + (37904474842917/2500000000000 : ℝ)*(major0) + (37904474842917/2500000000000 : ℝ)*(major1) + (37904474842917/2500000000000 : ℝ)*(major2) + (114980902300097/5000000000000 : ℝ)*(sp0) + (287452899431547/12500000000000 : ℝ)*(sp1) + (71863225776371/3125000000000 : ℝ)*(sp2) + (732731429206781/100000000000000 : ℝ)*(sp3) + (6047926777/100000000000000 : ℝ)*(sp4) + (1114857703/50000000000000 : ℝ)*(sp7) + (732733658922187/100000000000000 : ℝ)*(f.failure) + (1149812046964359/50000000000000 : ℝ)*(f.sum) + (983927314027/194000000000000000000000000 : ℝ)*base66 + (61510900343247251/9700000000000000000000000000000 : ℝ)*base68 + (12475084016352749/9700000000000000000000000000000 : ℝ)*base69 + (44485248495247251/9700000000000000000000000000000 : ℝ)*base72 + (409208218029/194000000000000000000000000 : ℝ)*base74 + (2733176093547251/9700000000000000000000000000000 : ℝ)*base76 + (111597621299247251/9700000000000000000000000000000 : ℝ)*base78 + (95521479054847251/9700000000000000000000000000000 : ℝ)*base80 + (735792894237/194000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (7117757/1250000000000000000000 : ℝ)*base89 + (7117757/1250000000000000000000 : ℝ)*base91 + (7117757/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (90743240976124434612944243/24250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10097577/2000000000000 : ℝ)*(base19) + (511821281/100000000000000 : ℝ)*(base23) + (73700573/50000000000000 : ℝ)*(lower1) + (1298357/1562500000000 : ℝ)*(upper3) + (7882597/50000000000000 : ℝ)*(lower4) + (1495081/2000000000000 : ℝ)*(upper5) + (391686076279027/25000000000000 : ℝ)*(major0) + (391686076279027/25000000000000 : ℝ)*(major1) + (391686076279027/25000000000000 : ℝ)*(major2) + (183674327/100000000000000 : ℝ)*(sp2) + (297039725060083/12500000000000 : ℝ)*(sp4) + (2376317295601813/100000000000000 : ℝ)*(sp5) + (475263420997011/20000000000000 : ℝ)*(sp6) + (75717068501857/10000000000000 : ℝ)*(sp7) + (75717068501857/10000000000000 : ℝ)*(f.failure) + (297039725060083/12500000000000 : ℝ)*(f.sum) + (3935740917871/1164000000000000000000000000 : ℝ)*base65 + (271932077843210581/97000000000000000000000000000000 : ℝ)*base68 + (117410521272789419/97000000000000000000000000000000 : ℝ)*base69 + (131784311072789419/97000000000000000000000000000000 : ℝ)*base71 + (492464587861/232800000000000000000000000 : ℝ)*base74 + (1045696441064789419/97000000000000000000000000000000 : ℝ)*base75 + (212676424336789419/97000000000000000000000000000000 : ℝ)*base77 + (221955802072789419/97000000000000000000000000000000 : ℝ)*base79 + (1062863633059/1164000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (11127/125000000000000000000 : ℝ)*base89 + (11127/125000000000000000000 : ℝ)*base91 + (11127/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1739_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (25865111/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9097/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4441/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2221/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18191/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1739_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1739_box_0 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-440286141/5000000000 : ℝ)*x 0 + (5437572429/10000000000 : ℝ)*x 1 + (2718786149/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (440286141/5000000000 : ℝ)^5599 ≤ (2555917901091/50000000000000 : ℝ)^4575 := by
    have hnat : (440286141 : ℕ)^5599*50000000000000^4575 ≤ 2555917901091^4575*5000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440286141 5000000000 2555917901091 50000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437572429/10000000000 : ℝ)^5599 ≤ (47444082792311/100000000000000 : ℝ)^4575 := by
    have hnat : (5437572429 : ℕ)^5599*100000000000000^4575 ≤ 47444082792311^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437572429 10000000000 47444082792311 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2718786149/5000000000 : ℝ)^5599 ≤ (741313771773/1562500000000 : ℝ)^4575 := by
    have hnat : (2718786149 : ℕ)^5599*1562500000000^4575 ≤ 741313771773^4575*5000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718786149 5000000000 741313771773 1562500000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-440286141/5000000000 : ℝ), (5437572429/10000000000 : ℝ), (2718786149/5000000000 : ℝ)] ![(2555917901091/50000000000000 : ℝ), (47444082792311/100000000000000 : ℝ), (741313771773/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-440286141/5000000000 : ℝ)|^5599 ≤ (2555917901091/50000000000000 : ℝ)^4575
        have hw : |(-440286141/5000000000 : ℝ)|=(440286141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437572429/10000000000 : ℝ)|^5599 ≤ (47444082792311/100000000000000 : ℝ)^4575
        have hw : |(5437572429/10000000000 : ℝ)|=(5437572429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2718786149/5000000000 : ℝ)|^5599 ≤ (741313771773/1562500000000 : ℝ)^4575
        have hw : |(2718786149/5000000000 : ℝ)|=(2718786149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_box_1 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2597610007/5000000000 : ℝ)*x 0 + (-61446121/500000000 : ℝ)*x 1 + (5437572523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2597610007/5000000000 : ℝ)^5599 ≤ (44869265299883/100000000000000 : ℝ)^4575 := by
    have hnat : (2597610007 : ℕ)^5599*100000000000000^4575 ≤ 44869265299883^4575*5000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597610007 5000000000 44869265299883 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (61446121/500000000 : ℝ)^5599 ≤ (3843325445677/50000000000000 : ℝ)^4575 := by
    have hnat : (61446121 : ℕ)^5599*50000000000000^4575 ≤ 3843325445677^4575*500000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61446121 500000000 3843325445677 50000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5437572523/10000000000 : ℝ)^5599 ≤ (23722041898029/50000000000000 : ℝ)^4575 := by
    have hnat : (5437572523 : ℕ)^5599*50000000000000^4575 ≤ 23722041898029^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437572523 10000000000 23722041898029 50000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2597610007/5000000000 : ℝ), (-61446121/500000000 : ℝ), (5437572523/10000000000 : ℝ)] ![(44869265299883/100000000000000 : ℝ), (3843325445677/50000000000000 : ℝ), (23722041898029/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2597610007/5000000000 : ℝ)|^5599 ≤ (44869265299883/100000000000000 : ℝ)^4575
        have hw : |(2597610007/5000000000 : ℝ)|=(2597610007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-61446121/500000000 : ℝ)|^5599 ≤ (3843325445677/50000000000000 : ℝ)^4575
        have hw : |(-61446121/500000000 : ℝ)|=(61446121/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5437572523/10000000000 : ℝ)|^5599 ≤ (23722041898029/50000000000000 : ℝ)^4575
        have hw : |(5437572523/10000000000 : ℝ)|=(5437572523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_box_2 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2597610099/5000000000 : ℝ)*x 0 + (1359393103/2500000000 : ℝ)*x 1 + (-15361529/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2597610099/5000000000 : ℝ)^5599 ≤ (11217316811179/25000000000000 : ℝ)^4575 := by
    have hnat : (2597610099 : ℕ)^5599*25000000000000^4575 ≤ 11217316811179^4575*5000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597610099 5000000000 11217316811179 25000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359393103/2500000000 : ℝ)^5599 ≤ (23722041305391/50000000000000 : ℝ)^4575 := by
    have hnat : (1359393103 : ℕ)^5599*50000000000000^4575 ≤ 23722041305391^4575*2500000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359393103 2500000000 23722041305391 50000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15361529/125000000 : ℝ)^5599 ≤ (7686650125877/100000000000000 : ℝ)^4575 := by
    have hnat : (15361529 : ℕ)^5599*100000000000000^4575 ≤ 7686650125877^4575*125000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15361529 125000000 7686650125877 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2597610099/5000000000 : ℝ), (1359393103/2500000000 : ℝ), (-15361529/125000000 : ℝ)] ![(11217316811179/25000000000000 : ℝ), (23722041305391/50000000000000 : ℝ), (7686650125877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2597610099/5000000000 : ℝ)|^5599 ≤ (11217316811179/25000000000000 : ℝ)^4575
        have hw : |(2597610099/5000000000 : ℝ)|=(2597610099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359393103/2500000000 : ℝ)|^5599 ≤ (23722041305391/50000000000000 : ℝ)^4575
        have hw : |(1359393103/2500000000 : ℝ)|=(1359393103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-15361529/125000000 : ℝ)|^5599 ≤ (7686650125877/100000000000000 : ℝ)^4575
        have hw : |(-15361529/125000000 : ℝ)|=(15361529/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_box_3 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2286546093/5000000000 : ℝ)*x 0 + (3821013651/10000000000 : ℝ)*x 1 + (3821013727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2286546093/5000000000 : ℝ)^5599 ≤ (38384545545937/100000000000000 : ℝ)^4575 := by
    have hnat : (2286546093 : ℕ)^5599*100000000000000^4575 ≤ 38384545545937^4575*5000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2286546093 5000000000 38384545545937 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3821013651/10000000000 : ℝ)^5599 ≤ (3850965855041/12500000000000 : ℝ)^4575 := by
    have hnat : (3821013651 : ℕ)^5599*12500000000000^4575 ≤ 3850965855041^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3821013651 10000000000 3850965855041 12500000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3821013727/10000000000 : ℝ)^5599 ≤ (15403863795123/50000000000000 : ℝ)^4575 := by
    have hnat : (3821013727 : ℕ)^5599*50000000000000^4575 ≤ 15403863795123^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3821013727 10000000000 15403863795123 50000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2286546093/5000000000 : ℝ), (3821013651/10000000000 : ℝ), (3821013727/10000000000 : ℝ)] ![(38384545545937/100000000000000 : ℝ), (3850965855041/12500000000000 : ℝ), (15403863795123/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2286546093/5000000000 : ℝ)|^5599 ≤ (38384545545937/100000000000000 : ℝ)^4575
        have hw : |(2286546093/5000000000 : ℝ)|=(2286546093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3821013651/10000000000 : ℝ)|^5599 ≤ (3850965855041/12500000000000 : ℝ)^4575
        have hw : |(3821013651/10000000000 : ℝ)|=(3821013651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3821013727/10000000000 : ℝ)|^5599 ≤ (15403863795123/50000000000000 : ℝ)^4575
        have hw : |(3821013727/10000000000 : ℝ)|=(3821013727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_box_4 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1732701063/10000000000 : ℝ)*x 0 + (5126884347/10000000000 : ℝ)*x 1 + (5126885247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1732701063/10000000000 : ℝ)^5599 ≤ (11703906858967/100000000000000 : ℝ)^4575 := by
    have hnat : (1732701063 : ℕ)^5599*100000000000000^4575 ≤ 11703906858967^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1732701063 10000000000 11703906858967 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5126884347/10000000000 : ℝ)^5599 ≤ (5518505227859/12500000000000 : ℝ)^4575 := by
    have hnat : (5126884347 : ℕ)^5599*12500000000000^4575 ≤ 5518505227859^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5126884347 10000000000 5518505227859 12500000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5126885247/10000000000 : ℝ)^5599 ≤ (44148051307489/100000000000000 : ℝ)^4575 := by
    have hnat : (5126885247 : ℕ)^5599*100000000000000^4575 ≤ 44148051307489^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5126885247 10000000000 44148051307489 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1732701063/10000000000 : ℝ), (5126884347/10000000000 : ℝ), (5126885247/10000000000 : ℝ)] ![(11703906858967/100000000000000 : ℝ), (5518505227859/12500000000000 : ℝ), (44148051307489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1732701063/10000000000 : ℝ)|^5599 ≤ (11703906858967/100000000000000 : ℝ)^4575
        have hw : |(-1732701063/10000000000 : ℝ)|=(1732701063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5126884347/10000000000 : ℝ)|^5599 ≤ (5518505227859/12500000000000 : ℝ)^4575
        have hw : |(5126884347/10000000000 : ℝ)|=(5126884347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5126885247/10000000000 : ℝ)|^5599 ≤ (44148051307489/100000000000000 : ℝ)^4575
        have hw : |(5126885247/10000000000 : ℝ)|=(5126885247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_box_5 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (675524199/1250000000 : ℝ)*x 0 + (-683980549/5000000000 : ℝ)*x 1 + (102537677/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (675524199/1250000000 : ℝ)^5599 ≤ (47087903522021/100000000000000 : ℝ)^4575 := by
    have hnat : (675524199 : ℕ)^5599*100000000000000^4575 ≤ 47087903522021^4575*1250000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675524199 1250000000 47087903522021 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (683980549/5000000000 : ℝ)^5599 ≤ (8764059866879/100000000000000 : ℝ)^4575 := by
    have hnat : (683980549 : ℕ)^5599*100000000000000^4575 ≤ 8764059866879^4575*5000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683980549 5000000000 8764059866879 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (102537677/200000000 : ℝ)^5599 ≤ (5518504573157/12500000000000 : ℝ)^4575 := by
    have hnat : (102537677 : ℕ)^5599*12500000000000^4575 ≤ 5518504573157^4575*200000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102537677 200000000 5518504573157 12500000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(675524199/1250000000 : ℝ), (-683980549/5000000000 : ℝ), (102537677/200000000 : ℝ)] ![(47087903522021/100000000000000 : ℝ), (8764059866879/100000000000000 : ℝ), (5518504573157/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(675524199/1250000000 : ℝ)|^5599 ≤ (47087903522021/100000000000000 : ℝ)^4575
        have hw : |(675524199/1250000000 : ℝ)|=(675524199/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-683980549/5000000000 : ℝ)|^5599 ≤ (8764059866879/100000000000000 : ℝ)^4575
        have hw : |(-683980549/5000000000 : ℝ)|=(683980549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(102537677/200000000 : ℝ)|^5599 ≤ (5518504573157/12500000000000 : ℝ)^4575
        have hw : |(102537677/200000000 : ℝ)|=(102537677/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_box_6 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2702096331/5000000000 : ℝ)*x 0 + (5126884489/10000000000 : ℝ)*x 1 + (-683980753/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2702096331/5000000000 : ℝ)^5599 ≤ (4708789360501/10000000000000 : ℝ)^4575 := by
    have hnat : (2702096331 : ℕ)^5599*10000000000000^4575 ≤ 4708789360501^4575*5000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702096331 5000000000 4708789360501 10000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5126884489/10000000000 : ℝ)^5599 ≤ (22074021659667/50000000000000 : ℝ)^4575 := by
    have hnat : (5126884489 : ℕ)^5599*50000000000000^4575 ≤ 22074021659667^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5126884489 10000000000 22074021659667 50000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (683980753/5000000000 : ℝ)^5599 ≤ (34234621351/390625000000 : ℝ)^4575 := by
    have hnat : (683980753 : ℕ)^5599*390625000000^4575 ≤ 34234621351^4575*5000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683980753 5000000000 34234621351 390625000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2702096331/5000000000 : ℝ), (5126884489/10000000000 : ℝ), (-683980753/5000000000 : ℝ)] ![(4708789360501/10000000000000 : ℝ), (22074021659667/50000000000000 : ℝ), (34234621351/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2702096331/5000000000 : ℝ)|^5599 ≤ (4708789360501/10000000000000 : ℝ)^4575
        have hw : |(2702096331/5000000000 : ℝ)|=(2702096331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5126884489/10000000000 : ℝ)|^5599 ≤ (22074021659667/50000000000000 : ℝ)^4575
        have hw : |(5126884489/10000000000 : ℝ)|=(5126884489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-683980753/5000000000 : ℝ)|^5599 ≤ (34234621351/390625000000 : ℝ)^4575
        have hw : |(-683980753/5000000000 : ℝ)|=(683980753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_box_7 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (435172843/1250000000 : ℝ)*x 0 + (43646769/100000000 : ℝ)*x 1 + (2182338081/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435172843/1250000000 : ℝ)^5599 ≤ (6872651289429/25000000000000 : ℝ)^4575 := by
    have hnat : (435172843 : ℕ)^5599*25000000000000^4575 ≤ 6872651289429^4575*1250000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435172843 1250000000 6872651289429 25000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43646769/100000000 : ℝ)^5599 ≤ (18127350581933/50000000000000 : ℝ)^4575 := by
    have hnat : (43646769 : ℕ)^5599*50000000000000^4575 ≤ 18127350581933^4575*100000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43646769 100000000 18127350581933 50000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2182338081/5000000000 : ℝ)^5599 ≤ (18127346830839/50000000000000 : ℝ)^4575 := by
    have hnat : (2182338081 : ℕ)^5599*50000000000000^4575 ≤ 18127346830839^4575*5000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182338081 5000000000 18127346830839 50000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(435172843/1250000000 : ℝ), (43646769/100000000 : ℝ), (2182338081/5000000000 : ℝ)] ![(6872651289429/25000000000000 : ℝ), (18127350581933/50000000000000 : ℝ), (18127346830839/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(435172843/1250000000 : ℝ)|^5599 ≤ (6872651289429/25000000000000 : ℝ)^4575
        have hw : |(435172843/1250000000 : ℝ)|=(435172843/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(43646769/100000000 : ℝ)|^5599 ≤ (18127350581933/50000000000000 : ℝ)^4575
        have hw : |(43646769/100000000 : ℝ)|=(43646769/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2182338081/5000000000 : ℝ)|^5599 ≤ (18127346830839/50000000000000 : ℝ)^4575
        have hw : |(2182338081/5000000000 : ℝ)|=(2182338081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_box_8 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-154775953/1000000000 : ℝ)*x 0 + (4891538837/10000000000 : ℝ)*x 1 + (687661501/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (154775953/1000000000 : ℝ)^5599 ≤ (10193862211091/100000000000000 : ℝ)^4575 := by
    have hnat : (154775953 : ℕ)^5599*100000000000000^4575 ≤ 10193862211091^4575*1000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      154775953 1000000000 10193862211091 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4891538837/10000000000 : ℝ)^5599 ≤ (41680757576977/100000000000000 : ℝ)^4575 := by
    have hnat : (4891538837 : ℕ)^5599*100000000000000^4575 ≤ 41680757576977^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4891538837 10000000000 41680757576977 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (687661501/1250000000 : ℝ)^5599 ≤ (24062690092749/50000000000000 : ℝ)^4575 := by
    have hnat : (687661501 : ℕ)^5599*50000000000000^4575 ≤ 24062690092749^4575*1250000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      687661501 1250000000 24062690092749 50000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-154775953/1000000000 : ℝ), (4891538837/10000000000 : ℝ), (687661501/1250000000 : ℝ)] ![(10193862211091/100000000000000 : ℝ), (41680757576977/100000000000000 : ℝ), (24062690092749/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-154775953/1000000000 : ℝ)|^5599 ≤ (10193862211091/100000000000000 : ℝ)^4575
        have hw : |(-154775953/1000000000 : ℝ)|=(154775953/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4891538837/10000000000 : ℝ)|^5599 ≤ (41680757576977/100000000000000 : ℝ)^4575
        have hw : |(4891538837/10000000000 : ℝ)|=(4891538837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(687661501/1250000000 : ℝ)|^5599 ≤ (24062690092749/50000000000000 : ℝ)^4575
        have hw : |(687661501/1250000000 : ℝ)|=(687661501/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_box_9 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5152416859/10000000000 : ℝ)*x 0 + (-1198883997/10000000000 : ℝ)*x 1 + (5501292759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5152416859/10000000000 : ℝ)^5599 ≤ (11104316259891/25000000000000 : ℝ)^4575 := by
    have hnat : (5152416859 : ℕ)^5599*25000000000000^4575 ≤ 11104316259891^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152416859 10000000000 11104316259891 25000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1198883997/10000000000 : ℝ)^5599 ≤ (372867336277/5000000000000 : ℝ)^4575 := by
    have hnat : (1198883997 : ℕ)^5599*5000000000000^4575 ≤ 372867336277^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1198883997 10000000000 372867336277 5000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5501292759/10000000000 : ℝ)^5599 ≤ (24062694112867/50000000000000 : ℝ)^4575 := by
    have hnat : (5501292759 : ℕ)^5599*50000000000000^4575 ≤ 24062694112867^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5501292759 10000000000 24062694112867 50000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5152416859/10000000000 : ℝ), (-1198883997/10000000000 : ℝ), (5501292759/10000000000 : ℝ)] ![(11104316259891/25000000000000 : ℝ), (372867336277/5000000000000 : ℝ), (24062694112867/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5152416859/10000000000 : ℝ)|^5599 ≤ (11104316259891/25000000000000 : ℝ)^4575
        have hw : |(5152416859/10000000000 : ℝ)|=(5152416859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1198883997/10000000000 : ℝ)|^5599 ≤ (372867336277/5000000000000 : ℝ)^4575
        have hw : |(-1198883997/10000000000 : ℝ)|=(1198883997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5501292759/10000000000 : ℝ)|^5599 ≤ (24062694112867/50000000000000 : ℝ)^4575
        have hw : |(5501292759/10000000000 : ℝ)|=(5501292759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_box_10 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (257620843/500000000 : ℝ)*x 0 + (85957697/156250000 : ℝ)*x 1 + (-74930263/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (257620843/500000000 : ℝ)^5599 ≤ (22208632525057/50000000000000 : ℝ)^4575 := by
    have hnat : (257620843 : ℕ)^5599*50000000000000^4575 ≤ 22208632525057^4575*500000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257620843 500000000 22208632525057 50000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (85957697/156250000 : ℝ)^5599 ≤ (24062693304561/50000000000000 : ℝ)^4575 := by
    have hnat : (85957697 : ℕ)^5599*50000000000000^4575 ≤ 24062693304561^4575*156250000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85957697 156250000 24062693304561 50000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (74930263/625000000 : ℝ)^5599 ≤ (298293933271/4000000000000 : ℝ)^4575 := by
    have hnat : (74930263 : ℕ)^5599*4000000000000^4575 ≤ 298293933271^4575*625000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74930263 625000000 298293933271 4000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(257620843/500000000 : ℝ), (85957697/156250000 : ℝ), (-74930263/625000000 : ℝ)] ![(22208632525057/50000000000000 : ℝ), (24062693304561/50000000000000 : ℝ), (298293933271/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(257620843/500000000 : ℝ)|^5599 ≤ (22208632525057/50000000000000 : ℝ)^4575
        have hw : |(257620843/500000000 : ℝ)|=(257620843/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(85957697/156250000 : ℝ)|^5599 ≤ (24062693304561/50000000000000 : ℝ)^4575
        have hw : |(85957697/156250000 : ℝ)|=(85957697/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-74930263/625000000 : ℝ)|^5599 ≤ (298293933271/4000000000000 : ℝ)^4575
        have hw : |(-74930263/625000000 : ℝ)|=(74930263/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_box_11 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4786297769/10000000000 : ℝ)*x 0 + (3709094667/10000000000 : ℝ)*x 1 + (370909447/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4786297769/10000000000 : ℝ)^5599 ≤ (4058593972173/10000000000000 : ℝ)^4575 := by
    have hnat : (4786297769 : ℕ)^5599*10000000000000^4575 ≤ 4058593972173^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4786297769 10000000000 4058593972173 10000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3709094667/10000000000 : ℝ)^5599 ≤ (29707031096437/100000000000000 : ℝ)^4575 := by
    have hnat : (3709094667 : ℕ)^5599*100000000000000^4575 ≤ 29707031096437^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3709094667 10000000000 29707031096437 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (370909447/1000000000 : ℝ)^5599 ≤ (29707029165461/100000000000000 : ℝ)^4575 := by
    have hnat : (370909447 : ℕ)^5599*100000000000000^4575 ≤ 29707029165461^4575*1000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370909447 1000000000 29707029165461 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4786297769/10000000000 : ℝ), (3709094667/10000000000 : ℝ), (370909447/1000000000 : ℝ)] ![(4058593972173/10000000000000 : ℝ), (29707031096437/100000000000000 : ℝ), (29707029165461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4786297769/10000000000 : ℝ)|^5599 ≤ (4058593972173/10000000000000 : ℝ)^4575
        have hw : |(4786297769/10000000000 : ℝ)|=(4786297769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3709094667/10000000000 : ℝ)|^5599 ≤ (29707031096437/100000000000000 : ℝ)^4575
        have hw : |(3709094667/10000000000 : ℝ)|=(3709094667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(370909447/1000000000 : ℝ)|^5599 ≤ (29707029165461/100000000000000 : ℝ)^4575
        have hw : |(370909447/1000000000 : ℝ)|=(370909447/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_box_12 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-526269363/5000000000 : ℝ)*x 0 + (2829257133/5000000000 : ℝ)*x 1 + (5096402581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526269363/5000000000 : ℝ)^5599 ≤ (1271804581001/20000000000000 : ℝ)^4575 := by
    have hnat : (526269363 : ℕ)^5599*20000000000000^4575 ≤ 1271804581001^4575*5000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526269363 5000000000 1271804581001 20000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2829257133/5000000000 : ℝ)^5599 ≤ (49813952171617/100000000000000 : ℝ)^4575 := by
    have hnat : (2829257133 : ℕ)^5599*100000000000000^4575 ≤ 49813952171617^4575*5000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2829257133 5000000000 49813952171617 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5096402581/10000000000 : ℝ)^5599 ≤ (8765404982827/20000000000000 : ℝ)^4575 := by
    have hnat : (5096402581 : ℕ)^5599*20000000000000^4575 ≤ 8765404982827^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5096402581 10000000000 8765404982827 20000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-526269363/5000000000 : ℝ), (2829257133/5000000000 : ℝ), (5096402581/10000000000 : ℝ)] ![(1271804581001/20000000000000 : ℝ), (49813952171617/100000000000000 : ℝ), (8765404982827/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-526269363/5000000000 : ℝ)|^5599 ≤ (1271804581001/20000000000000 : ℝ)^4575
        have hw : |(-526269363/5000000000 : ℝ)|=(526269363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2829257133/5000000000 : ℝ)|^5599 ≤ (49813952171617/100000000000000 : ℝ)^4575
        have hw : |(2829257133/5000000000 : ℝ)|=(2829257133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5096402581/10000000000 : ℝ)|^5599 ≤ (8765404982827/20000000000000 : ℝ)^4575
        have hw : |(5096402581/10000000000 : ℝ)|=(5096402581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_box_13 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (271238247/500000000 : ℝ)*x 0 + (-55235971/400000000 : ℝ)*x 1 + (5096403167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271238247/500000000 : ℝ)^5599 ≤ (1892294338567/4000000000000 : ℝ)^4575 := by
    have hnat : (271238247 : ℕ)^5599*4000000000000^4575 ≤ 1892294338567^4575*500000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271238247 500000000 1892294338567 4000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (55235971/400000000 : ℝ)^5599 ≤ (8865610438163/100000000000000 : ℝ)^4575 := by
    have hnat : (55235971 : ℕ)^5599*100000000000000^4575 ≤ 8865610438163^4575*400000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55235971 400000000 8865610438163 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5096403167/10000000000 : ℝ)^5599 ≤ (21913515540719/50000000000000 : ℝ)^4575 := by
    have hnat : (5096403167 : ℕ)^5599*50000000000000^4575 ≤ 21913515540719^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5096403167 10000000000 21913515540719 50000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(271238247/500000000 : ℝ), (-55235971/400000000 : ℝ), (5096403167/10000000000 : ℝ)] ![(1892294338567/4000000000000 : ℝ), (8865610438163/100000000000000 : ℝ), (21913515540719/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(271238247/500000000 : ℝ)|^5599 ≤ (1892294338567/4000000000000 : ℝ)^4575
        have hw : |(271238247/500000000 : ℝ)|=(271238247/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-55235971/400000000 : ℝ)|^5599 ≤ (8865610438163/100000000000000 : ℝ)^4575
        have hw : |(-55235971/400000000 : ℝ)|=(55235971/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5096403167/10000000000 : ℝ)|^5599 ≤ (21913515540719/50000000000000 : ℝ)^4575
        have hw : |(5096403167/10000000000 : ℝ)|=(5096403167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_box_14 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5424764697/10000000000 : ℝ)*x 0 + (5096402849/10000000000 : ℝ)*x 1 + (-1380900031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5424764697/10000000000 : ℝ)^5599 ≤ (47307355870751/100000000000000 : ℝ)^4575 := by
    have hnat : (5424764697 : ℕ)^5599*100000000000000^4575 ≤ 47307355870751^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424764697 10000000000 47307355870751 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5096402849/10000000000 : ℝ)^5599 ≤ (10956756933669/25000000000000 : ℝ)^4575 := by
    have hnat : (5096402849 : ℕ)^5599*25000000000000^4575 ≤ 10956756933669^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5096402849 10000000000 10956756933669 25000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1380900031/10000000000 : ℝ)^5599 ≤ (4432808189091/50000000000000 : ℝ)^4575 := by
    have hnat : (1380900031 : ℕ)^5599*50000000000000^4575 ≤ 4432808189091^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380900031 10000000000 4432808189091 50000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5424764697/10000000000 : ℝ), (5096402849/10000000000 : ℝ), (-1380900031/10000000000 : ℝ)] ![(47307355870751/100000000000000 : ℝ), (10956756933669/25000000000000 : ℝ), (4432808189091/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5424764697/10000000000 : ℝ)|^5599 ≤ (47307355870751/100000000000000 : ℝ)^4575
        have hw : |(5424764697/10000000000 : ℝ)|=(5424764697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5096402849/10000000000 : ℝ)|^5599 ≤ (10956756933669/25000000000000 : ℝ)^4575
        have hw : |(5096402849/10000000000 : ℝ)|=(5096402849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1380900031/10000000000 : ℝ)|^5599 ≤ (4432808189091/50000000000000 : ℝ)^4575
        have hw : |(-1380900031/10000000000 : ℝ)|=(1380900031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_box_15 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (421131771/1250000000 : ℝ)*x 0 + (4417802533/10000000000 : ℝ)*x 1 + (4417802467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (421131771/1250000000 : ℝ)^5599 ≤ (13204513658539/50000000000000 : ℝ)^4575 := by
    have hnat : (421131771 : ℕ)^5599*50000000000000^4575 ≤ 13204513658539^4575*1250000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421131771 1250000000 13204513658539 50000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4417802533/10000000000 : ℝ)^5599 ≤ (36795486673073/100000000000000 : ℝ)^4575 := by
    have hnat : (4417802533 : ℕ)^5599*100000000000000^4575 ≤ 36795486673073^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4417802533 10000000000 36795486673073 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4417802467/10000000000 : ℝ)^5599 ≤ (18397743000163/50000000000000 : ℝ)^4575 := by
    have hnat : (4417802467 : ℕ)^5599*50000000000000^4575 ≤ 18397743000163^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4417802467 10000000000 18397743000163 50000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(421131771/1250000000 : ℝ), (4417802533/10000000000 : ℝ), (4417802467/10000000000 : ℝ)] ![(13204513658539/50000000000000 : ℝ), (36795486673073/100000000000000 : ℝ), (18397743000163/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(421131771/1250000000 : ℝ)|^5599 ≤ (13204513658539/50000000000000 : ℝ)^4575
        have hw : |(421131771/1250000000 : ℝ)|=(421131771/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4417802533/10000000000 : ℝ)|^5599 ≤ (36795486673073/100000000000000 : ℝ)^4575
        have hw : |(4417802533/10000000000 : ℝ)|=(4417802533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4417802467/10000000000 : ℝ)|^5599 ≤ (18397743000163/50000000000000 : ℝ)^4575
        have hw : |(4417802467/10000000000 : ℝ)|=(4417802467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1739_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (25865111/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18191/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2221/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(13743/20000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(57561/100000 : ℝ) ∧ (40451/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (9269/10000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18191/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2221/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18191/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2221/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18191/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2221/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18191/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2221/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18191/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2221/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18191/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2221/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2221/25000 : ℝ) ^ (5583/1024 : ℝ) ≤ (185207149666121/100000000000000000000 : ℝ) := by
    have hpowers : (2221/25000 : ℝ)^5583 ≤ (185207149666121/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2221 : ℕ)^5583*100000000000000000000^1024 ≤ 185207149666121^1024*25000^5583 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2221 25000 185207149666121 100000000000000000000 5583 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2221/25000 : ℝ)) (X := (185207149666121/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5583 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18191/100000 : ℝ) ^ (5583/1024 : ℝ) ≤ (4608909494973761/50000000000000000000 : ℝ) := by
    have hpowers : (18191/100000 : ℝ)^5583 ≤ (4608909494973761/50000000000000000000 : ℝ)^1024 := by
      have hnat : (18191 : ℕ)^5583*50000000000000000000^1024 ≤ 4608909494973761^1024*100000^5583 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18191 100000 4608909494973761 50000000000000000000 5583 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18191/100000 : ℝ)) (X := (4608909494973761/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5583 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000185207149666121/50000000000000000000 : ℝ) ≤ (5000003396952077/5000000000000000 : ℝ) ^ (5583/1024 : ℝ) := by
    have hpowers : (50000185207149666121/50000000000000000000 : ℝ)^1024 ≤ (5000003396952077/5000000000000000 : ℝ)^5583 := by
      have hnat : (50000185207149666121 : ℕ)^1024*5000000000000000^5583 ≤ 5000003396952077^5583*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000185207149666121 50000000000000000000 5000003396952077 5000000000000000 1024 5583 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000003396952077/5000000000000000 : ℝ)) (X := (50000185207149666121/50000000000000000000 : ℝ)) (by norm_num) 5583 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100009403026139613643/100000000000000000000 : ℝ) ≤ (5000086228990901/5000000000000000 : ℝ) ^ (5583/1024 : ℝ) := by
    have hpowers : (100009403026139613643/100000000000000000000 : ℝ)^1024 ≤ (5000086228990901/5000000000000000 : ℝ)^5583 := by
      have hnat : (100009403026139613643 : ℕ)^1024*5000000000000000^5583 ≤ 5000086228990901^5583*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100009403026139613643 100000000000000000000 5000086228990901 5000000000000000 1024 5583 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000086228990901/5000000000000000 : ℝ)) (X := (100009403026139613643/100000000000000000000 : ℝ)) (by norm_num) 5583 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25004608909494973761/25000000000000000000 : ℝ) ≤ (200006762441189/200000000000000 : ℝ) ^ (5583/1024 : ℝ) := by
    have hpowers : (25004608909494973761/25000000000000000000 : ℝ)^1024 ≤ (200006762441189/200000000000000 : ℝ)^5583 := by
      have hnat : (25004608909494973761 : ℕ)^1024*200000000000000^5583 ≤ 200006762441189^5583*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004608909494973761 25000000000000000000 200006762441189 200000000000000 1024 5583 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200006762441189/200000000000000 : ℝ)) (X := (25004608909494973761/25000000000000000000 : ℝ)) (by norm_num) 5583 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(185207149666121/100000000000000000000 : ℝ) ≤ ((46533559855767155807/46535000000000000000 : ℝ)+2*(10354004853/58168750000000 : ℝ)*(2221/25000 : ℝ))^(5583/1024 : ℝ) := by
    rw [show (46533559855767155807/46535000000000000000 : ℝ)+2*(10354004853/58168750000000 : ℝ)*(2221/25000 : ℝ)=(5000003396952077/5000000000000000 : ℝ) by norm_num, show 1+2*(185207149666121/100000000000000000000 : ℝ)=(50000185207149666121/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4608909494973761/50000000000000000000 : ℝ)+(185207149666121/100000000000000000000 : ℝ) ≤ ((46533559855767155807/46535000000000000000 : ℝ)+(10354004853/58168750000000 : ℝ)*((18191/100000 : ℝ)+(2221/25000 : ℝ)))^(5583/1024 : ℝ) := by
    rw [show (46533559855767155807/46535000000000000000 : ℝ)+(10354004853/58168750000000 : ℝ)*((18191/100000 : ℝ)+(2221/25000 : ℝ))=(5000086228990901/5000000000000000 : ℝ) by norm_num, show 1+(4608909494973761/50000000000000000000 : ℝ)+(185207149666121/100000000000000000000 : ℝ)=(100009403026139613643/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4608909494973761/50000000000000000000 : ℝ) ≤ ((46533559855767155807/46535000000000000000 : ℝ)+2*(10354004853/58168750000000 : ℝ)*(18191/100000 : ℝ))^(5583/1024 : ℝ) := by
    rw [show (46533559855767155807/46535000000000000000 : ℝ)+2*(10354004853/58168750000000 : ℝ)*(18191/100000 : ℝ)=(200006762441189/200000000000000 : ℝ) by norm_num, show 1+2*(4608909494973761/50000000000000000000 : ℝ)=(25004608909494973761/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (46533559855767155807/46535000000000000000 : ℝ)*(X 1 0+X 2 0)+(10354004853/58168750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5583/1024 : ℝ)) (lo := (2221/25000 : ℝ)) (hi := (18191/100000 : ℝ)) (c := (46533559855767155807/46535000000000000000 : ℝ)) (alpha := (10354004853/58168750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (46533559855767155807/46535000000000000000 : ℝ)*(X 0 1+X 2 1)+(10354004853/58168750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5583/1024 : ℝ)) (lo := (2221/25000 : ℝ)) (hi := (18191/100000 : ℝ)) (c := (46533559855767155807/46535000000000000000 : ℝ)) (alpha := (10354004853/58168750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (46533559855767155807/46535000000000000000 : ℝ)*(X 0 2+X 1 2)+(10354004853/58168750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5583/1024 : ℝ)) (lo := (2221/25000 : ℝ)) (hi := (18191/100000 : ℝ)) (c := (46533559855767155807/46535000000000000000 : ℝ)) (alpha := (10354004853/58168750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-440286141/5000000000 : ℝ)*X 0 0+(5437572429/10000000000 : ℝ)*X 0 1+(2718786149/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2597610007/5000000000 : ℝ)*X 1 0+(-61446121/500000000 : ℝ)*X 1 1+(5437572523/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2597610099/5000000000 : ℝ)*X 2 0+(1359393103/2500000000 : ℝ)*X 2 1+(-15361529/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2286546093/5000000000 : ℝ)*X 0 0+(3821013651/10000000000 : ℝ)*X 0 1+(3821013727/10000000000 : ℝ)*X 0 2+(2286546093/5000000000 : ℝ)*X 1 0+(3821013651/10000000000 : ℝ)*X 1 1+(3821013727/10000000000 : ℝ)*X 1 2+(2286546093/5000000000 : ℝ)*X 2 0+(3821013651/10000000000 : ℝ)*X 2 1+(3821013727/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1732701063/10000000000 : ℝ)*X 0 0+(5126884347/10000000000 : ℝ)*X 0 1+(5126885247/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((675524199/1250000000 : ℝ)*X 1 0+(-683980549/5000000000 : ℝ)*X 1 1+(102537677/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2702096331/5000000000 : ℝ)*X 2 0+(5126884489/10000000000 : ℝ)*X 2 1+(-683980753/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((435172843/1250000000 : ℝ)*X 0 0+(43646769/100000000 : ℝ)*X 0 1+(2182338081/5000000000 : ℝ)*X 0 2+(435172843/1250000000 : ℝ)*X 1 0+(43646769/100000000 : ℝ)*X 1 1+(2182338081/5000000000 : ℝ)*X 1 2+(435172843/1250000000 : ℝ)*X 2 0+(43646769/100000000 : ℝ)*X 2 1+(2182338081/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-154775953/1000000000 : ℝ)*X 0 0+(4891538837/10000000000 : ℝ)*X 0 1+(687661501/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5152416859/10000000000 : ℝ)*X 1 0+(-1198883997/10000000000 : ℝ)*X 1 1+(5501292759/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((257620843/500000000 : ℝ)*X 2 0+(85957697/156250000 : ℝ)*X 2 1+(-74930263/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4786297769/10000000000 : ℝ)*X 0 0+(3709094667/10000000000 : ℝ)*X 0 1+(370909447/1000000000 : ℝ)*X 0 2+(4786297769/10000000000 : ℝ)*X 1 0+(3709094667/10000000000 : ℝ)*X 1 1+(370909447/1000000000 : ℝ)*X 1 2+(4786297769/10000000000 : ℝ)*X 2 0+(3709094667/10000000000 : ℝ)*X 2 1+(370909447/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-526269363/5000000000 : ℝ)*X 0 0+(2829257133/5000000000 : ℝ)*X 0 1+(5096402581/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((271238247/500000000 : ℝ)*X 1 0+(-55235971/400000000 : ℝ)*X 1 1+(5096403167/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5424764697/10000000000 : ℝ)*X 2 0+(5096402849/10000000000 : ℝ)*X 2 1+(-1380900031/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((421131771/1250000000 : ℝ)*X 0 0+(4417802533/10000000000 : ℝ)*X 0 1+(4417802467/10000000000 : ℝ)*X 0 2+(421131771/1250000000 : ℝ)*X 1 0+(4417802533/10000000000 : ℝ)*X 1 1+(4417802467/10000000000 : ℝ)*X 1 2+(421131771/1250000000 : ℝ)*X 2 0+(4417802533/10000000000 : ℝ)*X 2 1+(4417802467/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-13743/20000 : ℝ) ≤ (-799382629388355571316857597124391/1163375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (120893757/100000000000000 : ℝ)*(lower0) + (9776913/50000000000000 : ℝ)*(lower3) + (35570729/25000000000000 : ℝ)*(lower4) + (505897910412429/50000000000000 : ℝ)*(major0) + (505897910412429/50000000000000 : ℝ)*(major1) + (505897910412429/50000000000000 : ℝ)*(major2) + (775921249/12500000000000 : ℝ)*(sp1) + (1521149147/25000000000000 : ℝ)*(sp2) + (311503387838771/20000000000000 : ℝ)*(sp4) + (48672263428067/3125000000000 : ℝ)*(sp5) + (1557512552471549/100000000000000 : ℝ)*(sp6) + (488976267577939/100000000000000 : ℝ)*(sp7) + (848937141/50000000000000 : ℝ)*(sp12) + (863056093/100000000000000 : ℝ)*(sp15) + (30561070664627/6250000000000 : ℝ)*(f.failure) + (1557518637068137/100000000000000 : ℝ)*(f.sum) + (164927641056979/46535000000000000000000000000 : ℝ)*base65 + (20155905683818574797/2326750000000000000000000000000000 : ℝ)*base68 + (3456968007686074797/2326750000000000000000000000000000 : ℝ)*base70 + (10228992244913925203/2326750000000000000000000000000000 : ℝ)*base71 + (92451599486389/46535000000000000000000000000 : ℝ)*base73 + (1529546916191824797/2326750000000000000000000000000000 : ℝ)*base76 + (9987079196306574797/2326750000000000000000000000000000 : ℝ)*base78 + (13185400326396425203/2326750000000000000000000000000000 : ℝ)*base79 + (24353924195659/46535000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (816097/78125000000000000000 : ℝ)*base89 + (816097/78125000000000000000 : ℝ)*base91 + (816097/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (57561/100000 : ℝ) ≤ (669677360387209642771637190612507/1163375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5549293/20000000000000 : ℝ)*(lower1) + (718853/2000000000000 : ℝ)*(lower2) + (9860701/100000000000000 : ℝ)*(lower5) + (1128807030939367/100000000000000 : ℝ)*(major0) + (1128807030939367/100000000000000 : ℝ)*(major1) + (1128807030939367/100000000000000 : ℝ)*(major2) + (846450108394317/50000000000000 : ℝ)*(sp0) + (1692900091126639/100000000000000 : ℝ)*(sp1) + (13543198894009/800000000000 : ℝ)*(sp2) + (545525856011131/100000000000000 : ℝ)*(sp3) + (74414121/25000000000000 : ℝ)*(sp5) + (263515999/50000000000000 : ℝ)*(sp6) + (20638693/50000000000000 : ℝ)*(sp7) + (171994489/100000000000000 : ℝ)*(sp8) + (545525897288517/100000000000000 : ℝ)*(f.failure) + (1692900388783123/100000000000000 : ℝ)*(f.sum) + (7184610538747/1454218750000000000000000000 : ℝ)*base66 + (15361179075360245831/4653500000000000000000000000000000 : ℝ)*base68 + (4962927057095745831/4653500000000000000000000000000000 : ℝ)*base70 + (6530600049684245831/4653500000000000000000000000000000 : ℝ)*base72 + (354949421880099/46535000000000000000000000000 : ℝ)*base74 + (7251140274181245831/4653500000000000000000000000000000 : ℝ)*base76 + (35794683689316245831/4653500000000000000000000000000000 : ℝ)*base78 + (6927218740339254169/4653500000000000000000000000000000 : ℝ)*base79 + (238987082955019/46535000000000000000000000000 : ℝ)*base82 + (3730387/1250000000000000000000 : ℝ)*base89 + (3730387/1250000000000000000000 : ℝ)*base91 + (3730387/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (40451/50000 : ℝ) ≤ (470610314205911039245841409096837/581687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (825953/3125000000000 : ℝ)*(upper2) + (34074821/100000000000000 : ℝ)*(upper3) + (5465393/50000000000000 : ℝ)*(upper4) + (549531929867097/50000000000000 : ℝ)*(major0) + (549531929867097/50000000000000 : ℝ)*(major1) + (549531929867097/50000000000000 : ℝ)*(major2) + (554761107/100000000000000 : ℝ)*(sp0) + (14536150497/100000000000000 : ℝ)*(sp1) + (2719157161/25000000000000 : ℝ)*(sp2) + (1285425271/50000000000000 : ℝ)*(sp3) + (820003668096579/50000000000000 : ℝ)*(sp8) + (204999169350471/12500000000000 : ℝ)*(sp9) + (1639997014325621/100000000000000 : ℝ)*(sp10) + (265574575561319/50000000000000 : ℝ)*(sp11) + (26557586098659/5000000000000 : ℝ)*(f.failure) + (328001578190853/20000000000000 : ℝ)*(f.sum) + (953849116367/727109375000000000000000000 : ℝ)*base66 + (12075801985129832279/2326750000000000000000000000000000 : ℝ)*base67 + (35485016734532417721/2326750000000000000000000000000000 : ℝ)*base70 + (4530246658637417721/2326750000000000000000000000000000 : ℝ)*base72 + (5396237095701/5816875000000000000000000000 : ℝ)*base74 + (18647757221470167721/2326750000000000000000000000000000 : ℝ)*base76 + (44583269943115917721/2326750000000000000000000000000000 : ℝ)*base78 + (13286430896452417721/2326750000000000000000000000000000 : ℝ)*base80 + (153088151227949/23267500000000000000000000000 : ℝ)*base82 + (736149/62500000000000000000 : ℝ)*base89 + (736149/62500000000000000000 : ℝ)*base91 + (736149/62500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-9269/10000 : ℝ) ≤ (-539152500461188769423780093333637/581687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (39749227/50000000000000 : ℝ)*(lower0) + (195947/10000000000000 : ℝ)*(lower1) + (69816207/50000000000000 : ℝ)*(lower4) + (288139961480397/25000000000000 : ℝ)*(major0) + (288139961480397/25000000000000 : ℝ)*(major1) + (288139961480397/25000000000000 : ℝ)*(major2) + (556796699/12500000000000 : ℝ)*(sp0) + (8149291213/50000000000000 : ℝ)*(sp5) + (6315896313/10000000000000 : ℝ)*(sp6) + (4055267671/50000000000000 : ℝ)*(sp7) + (1779006048025973/100000000000000 : ℝ)*(sp12) + (1778994203817139/100000000000000 : ℝ)*(sp13) + (444736835859109/25000000000000 : ℝ)*(sp14) + (556996963752561/100000000000000 : ℝ)*(sp15) + (278502537143951/50000000000000 : ℝ)*(f.failure) + (889505251199783/50000000000000 : ℝ)*(f.sum) + (79131037466683/23267500000000000000000000000 : ℝ)*base66 + (1661789782576390379/1163375000000000000000000000000000 : ℝ)*base67 + (4820220840083015379/1163375000000000000000000000000000 : ℝ)*base69 + (666381761033515379/1163375000000000000000000000000000 : ℝ)*base71 + (35287892631797/5816875000000000000000000000 : ℝ)*base74 + (3787715541172015379/1163375000000000000000000000000000 : ℝ)*base75 + (4289050232428984621/1163375000000000000000000000000000 : ℝ)*base78 + (27093083619053109621/1163375000000000000000000000000000 : ℝ)*base80 + (53810636174199/46535000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (9406439/625000000000000000000 : ℝ)*base90 + (9406439/625000000000000000000 : ℝ)*base92 + (9406439/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1739_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (25865111/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18191/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2221/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(13743/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(57561/100000 : ℝ) else (40451/50000 : ℝ) ≤ X j i ∧ X j i ≤ (9269/10000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1739_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1739_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (25865111/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9097/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4441/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(13743/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(57561/100000 : ℝ) else (40451/50000 : ℝ) ≤ X j i ∧ X j i ≤ (9269/10000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1739_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1739_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (25865111/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9097/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4441/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(13743/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(57561/100000 : ℝ) else (40451/50000 : ℝ) ≤ X j i ∧ X j i ≤ (9269/10000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1739_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1630_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:59:55.13999+00:00
-- url     : https://prove2.me/submissions/49cd9189-a565-4dab-8739-c150f1afdb7a

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
theorem support_rectangle_w1630_s0_0 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-382102323/2500000000 : ℝ)*x 0 + (1162126643/2000000000 : ℝ)*x 1 + (4907634387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (382102323/2500000000 : ℝ)^4839 ≤ (1846324554373/20000000000000 : ℝ)^3815 := by
    have hnat : (382102323 : ℕ)^4839*20000000000000^3815 ≤ 1846324554373^3815*2500000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      382102323 2500000000 1846324554373 20000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1162126643/2000000000 : ℝ)^4839 ≤ (5022705357213/10000000000000 : ℝ)^3815 := by
    have hnat : (1162126643 : ℕ)^4839*10000000000000^3815 ≤ 5022705357213^3815*2000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1162126643 2000000000 5022705357213 10000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4907634387/10000000000 : ℝ)^4839 ≤ (4054132364007/10000000000000 : ℝ)^3815 := by
    have hnat : (4907634387 : ℕ)^4839*10000000000000^3815 ≤ 4054132364007^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4907634387 10000000000 4054132364007 10000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-382102323/2500000000 : ℝ), (1162126643/2000000000 : ℝ), (4907634387/10000000000 : ℝ)] ![(1846324554373/20000000000000 : ℝ), (5022705357213/10000000000000 : ℝ), (4054132364007/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-382102323/2500000000 : ℝ)|^4839 ≤ (1846324554373/20000000000000 : ℝ)^3815
        have hw : |(-382102323/2500000000 : ℝ)|=(382102323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1162126643/2000000000 : ℝ)|^4839 ≤ (5022705357213/10000000000000 : ℝ)^3815
        have hw : |(1162126643/2000000000 : ℝ)|=(1162126643/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4907634387/10000000000 : ℝ)|^4839 ≤ (4054132364007/10000000000000 : ℝ)^3815
        have hw : |(4907634387/10000000000 : ℝ)|=(4907634387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s0_1 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5445548231/10000000000 : ℝ)*x 0 + (-506544069/2500000000 : ℝ)*x 1 + (981527181/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5445548231/10000000000 : ℝ)^4839 ≤ (46258488762283/100000000000000 : ℝ)^3815 := by
    have hnat : (5445548231 : ℕ)^4839*100000000000000^3815 ≤ 46258488762283^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5445548231 10000000000 46258488762283 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (506544069/2500000000 : ℝ)^4839 ≤ (13200171682667/100000000000000 : ℝ)^3815 := by
    have hnat : (506544069 : ℕ)^4839*100000000000000^3815 ≤ 13200171682667^3815*2500000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506544069 2500000000 13200171682667 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (981527181/2000000000 : ℝ)^4839 ≤ (40541339545983/100000000000000 : ℝ)^3815 := by
    have hnat : (981527181 : ℕ)^4839*100000000000000^3815 ≤ 40541339545983^3815*2000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      981527181 2000000000 40541339545983 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5445548231/10000000000 : ℝ), (-506544069/2500000000 : ℝ), (981527181/2000000000 : ℝ)] ![(46258488762283/100000000000000 : ℝ), (13200171682667/100000000000000 : ℝ), (40541339545983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5445548231/10000000000 : ℝ)|^4839 ≤ (46258488762283/100000000000000 : ℝ)^3815
        have hw : |(5445548231/10000000000 : ℝ)|=(5445548231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-506544069/2500000000 : ℝ)|^4839 ≤ (13200171682667/100000000000000 : ℝ)^3815
        have hw : |(-506544069/2500000000 : ℝ)|=(506544069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(981527181/2000000000 : ℝ)|^4839 ≤ (40541339545983/100000000000000 : ℝ)^3815
        have hw : |(981527181/2000000000 : ℝ)|=(981527181/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s0_2 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (680693571/1250000000 : ℝ)*x 0 + (2453817431/5000000000 : ℝ)*x 1 + (-1013088579/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (680693571/1250000000 : ℝ)^4839 ≤ (9251698478681/20000000000000 : ℝ)^3815 := by
    have hnat : (680693571 : ℕ)^4839*20000000000000^3815 ≤ 9251698478681^3815*1250000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680693571 1250000000 9251698478681 20000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2453817431/5000000000 : ℝ)^4839 ≤ (158364564911/390625000000 : ℝ)^3815 := by
    have hnat : (2453817431 : ℕ)^4839*390625000000^3815 ≤ 158364564911^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2453817431 5000000000 158364564911 390625000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1013088579/5000000000 : ℝ)^4839 ≤ (2640035794213/20000000000000 : ℝ)^3815 := by
    have hnat : (1013088579 : ℕ)^4839*20000000000000^3815 ≤ 2640035794213^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013088579 5000000000 2640035794213 20000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(680693571/1250000000 : ℝ), (2453817431/5000000000 : ℝ), (-1013088579/5000000000 : ℝ)] ![(9251698478681/20000000000000 : ℝ), (158364564911/390625000000 : ℝ), (2640035794213/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(680693571/1250000000 : ℝ)|^4839 ≤ (9251698478681/20000000000000 : ℝ)^3815
        have hw : |(680693571/1250000000 : ℝ)|=(680693571/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2453817431/5000000000 : ℝ)|^4839 ≤ (158364564911/390625000000 : ℝ)^3815
        have hw : |(2453817431/5000000000 : ℝ)|=(2453817431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1013088579/5000000000 : ℝ)|^4839 ≤ (2640035794213/20000000000000 : ℝ)^3815
        have hw : |(-1013088579/5000000000 : ℝ)|=(1013088579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s0_3 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4100084357/10000000000 : ℝ)*x 0 + (769505379/2500000000 : ℝ)*x 1 + (1071109251/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4100084357/10000000000 : ℝ)^4839 ≤ (32274602106319/100000000000000 : ℝ)^3815 := by
    have hnat : (4100084357 : ℕ)^4839*100000000000000^3815 ≤ 32274602106319^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4100084357 10000000000 32274602106319 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (769505379/2500000000 : ℝ)^4839 ≤ (2243450642501/10000000000000 : ℝ)^3815 := by
    have hnat : (769505379 : ℕ)^4839*10000000000000^3815 ≤ 2243450642501^3815*2500000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      769505379 2500000000 2243450642501 10000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1071109251/2000000000 : ℝ)^4839 ≤ (45290891462987/100000000000000 : ℝ)^3815 := by
    have hnat : (1071109251 : ℕ)^4839*100000000000000^3815 ≤ 45290891462987^3815*2000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071109251 2000000000 45290891462987 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4100084357/10000000000 : ℝ), (769505379/2500000000 : ℝ), (1071109251/2000000000 : ℝ)] ![(32274602106319/100000000000000 : ℝ), (2243450642501/10000000000000 : ℝ), (45290891462987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4100084357/10000000000 : ℝ)|^4839 ≤ (32274602106319/100000000000000 : ℝ)^3815
        have hw : |(4100084357/10000000000 : ℝ)|=(4100084357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(769505379/2500000000 : ℝ)|^4839 ≤ (2243450642501/10000000000000 : ℝ)^3815
        have hw : |(769505379/2500000000 : ℝ)|=(769505379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1071109251/2000000000 : ℝ)|^4839 ≤ (45290891462987/100000000000000 : ℝ)^3815
        have hw : |(1071109251/2000000000 : ℝ)|=(1071109251/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s0_4 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1530943907/10000000000 : ℝ)*x 0 + (1232567241/2500000000 : ℝ)*x 1 + (5787204323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1530943907/10000000000 : ℝ)^4839 ≤ (9251045403249/100000000000000 : ℝ)^3815 := by
    have hnat : (1530943907 : ℕ)^4839*100000000000000^3815 ≤ 9251045403249^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1530943907 10000000000 9251045403249 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1232567241/2500000000 : ℝ)^4839 ≤ (509732999601/1250000000000 : ℝ)^3815 := by
    have hnat : (1232567241 : ℕ)^4839*1250000000000^3815 ≤ 509732999601^3815*2500000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1232567241 2500000000 509732999601 1250000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5787204323/10000000000 : ℝ)^4839 ≤ (9994062924031/20000000000000 : ℝ)^3815 := by
    have hnat : (5787204323 : ℕ)^4839*20000000000000^3815 ≤ 9994062924031^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5787204323 10000000000 9994062924031 20000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1530943907/10000000000 : ℝ), (1232567241/2500000000 : ℝ), (5787204323/10000000000 : ℝ)] ![(9251045403249/100000000000000 : ℝ), (509732999601/1250000000000 : ℝ), (9994062924031/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1530943907/10000000000 : ℝ)|^4839 ≤ (9251045403249/100000000000000 : ℝ)^3815
        have hw : |(-1530943907/10000000000 : ℝ)|=(1530943907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1232567241/2500000000 : ℝ)|^4839 ≤ (509732999601/1250000000000 : ℝ)^3815
        have hw : |(1232567241/2500000000 : ℝ)|=(1232567241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5787204323/10000000000 : ℝ)|^4839 ≤ (9994062924031/20000000000000 : ℝ)^3815
        have hw : |(5787204323/10000000000 : ℝ)|=(5787204323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s0_5 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5199005461/10000000000 : ℝ)*x 0 + (-1146608549/10000000000 : ℝ)*x 1 + (5787203591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5199005461/10000000000 : ℝ)^4839 ≤ (21809176054089/50000000000000 : ℝ)^3815 := by
    have hnat : (5199005461 : ℕ)^4839*50000000000000^3815 ≤ 21809176054089^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5199005461 10000000000 21809176054089 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1146608549/10000000000 : ℝ)^4839 ≤ (3205670637611/50000000000000 : ℝ)^3815 := by
    have hnat : (1146608549 : ℕ)^4839*50000000000000^3815 ≤ 3205670637611^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1146608549 10000000000 3205670637611 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5787203591/10000000000 : ℝ)^4839 ≤ (49970306603089/100000000000000 : ℝ)^3815 := by
    have hnat : (5787203591 : ℕ)^4839*100000000000000^3815 ≤ 49970306603089^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5787203591 10000000000 49970306603089 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5199005461/10000000000 : ℝ), (-1146608549/10000000000 : ℝ), (5787203591/10000000000 : ℝ)] ![(21809176054089/50000000000000 : ℝ), (3205670637611/50000000000000 : ℝ), (49970306603089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5199005461/10000000000 : ℝ)|^4839 ≤ (21809176054089/50000000000000 : ℝ)^3815
        have hw : |(5199005461/10000000000 : ℝ)|=(5199005461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1146608549/10000000000 : ℝ)|^4839 ≤ (3205670637611/50000000000000 : ℝ)^3815
        have hw : |(-1146608549/10000000000 : ℝ)|=(1146608549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5787203591/10000000000 : ℝ)|^4839 ≤ (49970306603089/100000000000000 : ℝ)^3815
        have hw : |(5787203591/10000000000 : ℝ)|=(5787203591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s0_6 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2599501771/5000000000 : ℝ)*x 0 + (2893603231/5000000000 : ℝ)*x 1 + (-229321399/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2599501771/5000000000 : ℝ)^4839 ≤ (43618331686801/100000000000000 : ℝ)^3815 := by
    have hnat : (2599501771 : ℕ)^4839*100000000000000^3815 ≤ 43618331686801^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2599501771 5000000000 43618331686801 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2893603231/5000000000 : ℝ)^4839 ≤ (1561573063971/3125000000000 : ℝ)^3815 := by
    have hnat : (2893603231 : ℕ)^4839*3125000000000^3815 ≤ 1561573063971^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2893603231 5000000000 1561573063971 3125000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (229321399/2000000000 : ℝ)^4839 ≤ (3205665126797/50000000000000 : ℝ)^3815 := by
    have hnat : (229321399 : ℕ)^4839*50000000000000^3815 ≤ 3205665126797^3815*2000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229321399 2000000000 3205665126797 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2599501771/5000000000 : ℝ), (2893603231/5000000000 : ℝ), (-229321399/2000000000 : ℝ)] ![(43618331686801/100000000000000 : ℝ), (1561573063971/3125000000000 : ℝ), (3205665126797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2599501771/5000000000 : ℝ)|^4839 ≤ (43618331686801/100000000000000 : ℝ)^3815
        have hw : |(2599501771/5000000000 : ℝ)|=(2599501771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2893603231/5000000000 : ℝ)|^4839 ≤ (1561573063971/3125000000000 : ℝ)^3815
        have hw : |(2893603231/5000000000 : ℝ)|=(2893603231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-229321399/2000000000 : ℝ)|^4839 ≤ (3205665126797/50000000000000 : ℝ)^3815
        have hw : |(-229321399/2000000000 : ℝ)|=(229321399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s0_7 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2053236463/5000000000 : ℝ)*x 0 + (1059691601/2000000000 : ℝ)*x 1 + (3137112147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2053236463/5000000000 : ℝ)^4839 ≤ (1293536101113/4000000000000 : ℝ)^3815 := by
    have hnat : (2053236463 : ℕ)^4839*4000000000000^3815 ≤ 1293536101113^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2053236463 5000000000 1293536101113 4000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1059691601/2000000000 : ℝ)^4839 ≤ (44679398402507/100000000000000 : ℝ)^3815 := by
    have hnat : (1059691601 : ℕ)^4839*100000000000000^3815 ≤ 44679398402507^3815*2000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059691601 2000000000 44679398402507 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3137112147/10000000000 : ℝ)^4839 ≤ (2298219905149/10000000000000 : ℝ)^3815 := by
    have hnat : (3137112147 : ℕ)^4839*10000000000000^3815 ≤ 2298219905149^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3137112147 10000000000 2298219905149 10000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2053236463/5000000000 : ℝ), (1059691601/2000000000 : ℝ), (3137112147/10000000000 : ℝ)] ![(1293536101113/4000000000000 : ℝ), (44679398402507/100000000000000 : ℝ), (2298219905149/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2053236463/5000000000 : ℝ)|^4839 ≤ (1293536101113/4000000000000 : ℝ)^3815
        have hw : |(2053236463/5000000000 : ℝ)|=(2053236463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1059691601/2000000000 : ℝ)|^4839 ≤ (44679398402507/100000000000000 : ℝ)^3815
        have hw : |(1059691601/2000000000 : ℝ)|=(1059691601/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3137112147/10000000000 : ℝ)|^4839 ≤ (2298219905149/10000000000000 : ℝ)^3815
        have hw : |(3137112147/10000000000 : ℝ)|=(3137112147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1630_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35221777/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (889/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (23791/100000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4835/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4835 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4835*1^1024 ≤ 0^1024*1^4835 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4835 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4835 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4835/1024 : ℝ) ≤ (33036554955715383/2500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4835 ≤ (33036554955715383/2500000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4835*2500000000000000000^1024 ≤ 33036554955715383^1024*5^4835 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 33036554955715383 2500000000000000000 4835 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (33036554955715383/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4835 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4835/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4835 := by
      have hnat : (1 : ℕ)^1024*1^4835 ≤ 1^4835*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4835 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4835 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2533036554955715383/2500000000000000000 : ℝ) ≤ (10027842502765939/10000000000000000 : ℝ) ^ (4835/1024 : ℝ) := by
    have hpowers : (2533036554955715383/2500000000000000000 : ℝ)^1024 ≤ (10027842502765939/10000000000000000 : ℝ)^4835 := by
      have hnat : (2533036554955715383 : ℕ)^1024*10000000000000000^4835 ≤ 10027842502765939^4835*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2533036554955715383 2500000000000000000 10027842502765939 10000000000000000 1024 4835 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10027842502765939/10000000000000000 : ℝ)) (X := (2533036554955715383/2500000000000000000 : ℝ)) (by norm_num) 4835 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1283036554955715383/1250000000000000000 : ℝ) ≤ (5027842502765939/5000000000000000 : ℝ) ^ (4835/1024 : ℝ) := by
    have hpowers : (1283036554955715383/1250000000000000000 : ℝ)^1024 ≤ (5027842502765939/5000000000000000 : ℝ)^4835 := by
      have hnat : (1283036554955715383 : ℕ)^1024*5000000000000000^4835 ≤ 5027842502765939^4835*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1283036554955715383 1250000000000000000 5027842502765939 5000000000000000 1024 4835 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5027842502765939/5000000000000000 : ℝ)) (X := (1283036554955715383/1250000000000000000 : ℝ)) (by norm_num) 4835 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(27842502765939/4000000000000000 : ℝ)*(0 : ℝ))^(4835/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(27842502765939/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33036554955715383/2500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(27842502765939/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4835/1024 : ℝ) := by
    rw [show (1 : ℝ)+(27842502765939/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10027842502765939/10000000000000000 : ℝ) by norm_num, show 1+(33036554955715383/2500000000000000000 : ℝ)+(0 : ℝ)=(2533036554955715383/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33036554955715383/2500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(27842502765939/4000000000000000 : ℝ)*(2/5 : ℝ))^(4835/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(27842502765939/4000000000000000 : ℝ)*(2/5 : ℝ)=(5027842502765939/5000000000000000 : ℝ) by norm_num, show 1+2*(33036554955715383/2500000000000000000 : ℝ)=(1283036554955715383/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(27842502765939/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4835/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27842502765939/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(27842502765939/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4835/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27842502765939/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(27842502765939/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4835/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27842502765939/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-382102323/2500000000 : ℝ)*X 0 0+(1162126643/2000000000 : ℝ)*X 0 1+(4907634387/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5445548231/10000000000 : ℝ)*X 1 0+(-506544069/2500000000 : ℝ)*X 1 1+(981527181/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((680693571/1250000000 : ℝ)*X 2 0+(2453817431/5000000000 : ℝ)*X 2 1+(-1013088579/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4100084357/10000000000 : ℝ)*X 0 0+(769505379/2500000000 : ℝ)*X 0 1+(1071109251/2000000000 : ℝ)*X 0 2+(4100084357/10000000000 : ℝ)*X 1 0+(769505379/2500000000 : ℝ)*X 1 1+(1071109251/2000000000 : ℝ)*X 1 2+(4100084357/10000000000 : ℝ)*X 2 0+(769505379/2500000000 : ℝ)*X 2 1+(1071109251/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1530943907/10000000000 : ℝ)*X 0 0+(1232567241/2500000000 : ℝ)*X 0 1+(5787204323/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5199005461/10000000000 : ℝ)*X 1 0+(-1146608549/10000000000 : ℝ)*X 1 1+(5787203591/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2599501771/5000000000 : ℝ)*X 2 0+(2893603231/5000000000 : ℝ)*X 2 1+(-229321399/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2053236463/5000000000 : ℝ)*X 0 0+(1059691601/2000000000 : ℝ)*X 0 1+(3137112147/10000000000 : ℝ)*X 0 2+(2053236463/5000000000 : ℝ)*X 1 0+(1059691601/2000000000 : ℝ)*X 1 1+(3137112147/10000000000 : ℝ)*X 1 2+(2053236463/5000000000 : ℝ)*X 2 0+(1059691601/2000000000 : ℝ)*X 2 1+(3137112147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17643383838944825268309/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1293949549/100000000000000 : ℝ)*(base19) + (1342556939/100000000000000 : ℝ)*(base23) + (333379761/100000000000000 : ℝ)*(upper3) + (5425551/50000000000000 : ℝ)*(upper4) + (21490683/50000000000000 : ℝ)*(upper5) + (48328538920723/6250000000000 : ℝ)*(major0) + (48328538920723/6250000000000 : ℝ)*(major1) + (48328538920723/6250000000000 : ℝ)*(major2) + (138428585808219/12500000000000 : ℝ)*(sp0) + (27685825124371/2500000000000 : ℝ)*(sp1) + (1107432956367451/100000000000000 : ℝ)*(sp2) + (219537705108193/50000000000000 : ℝ)*(sp3) + (5612458637/100000000000000 : ℝ)*(sp4) + (825269309/25000000000000 : ℝ)*(sp7) + (439078711293623/100000000000000 : ℝ)*(f.failure) + (1107434298924389/100000000000000 : ℝ)*(f.sum) + (84599545716397/12500000000000000000000000000 : ℝ)*base65 + (175810593053897/25000000000000000000000000000 : ℝ)*base67 + (2220798228897/25000000000000000000000000000 : ℝ)*base69 + (204388986203897/25000000000000000000000000000 : ℝ)*base71 + (48912101703897/12500000000000000000000000000 : ℝ)*base73 + (110032587603897/25000000000000000000000000000 : ℝ)*base75 + (76555183003897/25000000000000000000000000000 : ℝ)*base77 + (27781457296103/25000000000000000000000000000 : ℝ)*base80 + (18843397353897/12500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (10828071/2000000000000000000000 : ℝ)*base89 + (10828071/2000000000000000000000 : ℝ)*base91 + (10828071/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (893258661221567175670263/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (186821691/20000000000000 : ℝ)*(base19) + (1670380511/100000000000000 : ℝ)*(base23) + (1225983843/100000000000000 : ℝ)*(base39) + (413101/25000000000000 : ℝ)*(upper2) + (674527/97656250000 : ℝ)*(upper5) + (814807231423761/100000000000000 : ℝ)*(major0) + (814807231423761/100000000000000 : ℝ)*(major1) + (407403002719959/50000000000000 : ℝ)*(major2) + (3502866609/100000000000000 : ℝ)*(sp1) + (507625163/20000000000000 : ℝ)*(sp2) + (116694052401727/10000000000000 : ℝ)*(sp4) + (233387217408441/20000000000000 : ℝ)*(sp5) + (291734385373697/25000000000000 : ℝ)*(sp6) + (92534483018703/20000000000000 : ℝ)*(sp7) + (92534483018703/20000000000000 : ℝ)*(f.failure) + (1166941750001113/100000000000000 : ℝ)*(f.sum) + (1214754587429581/400000000000000000000000000000 : ℝ)*base65 + (538871430323499/200000000000000000000000000000 : ℝ)*base68 + (3037285540076579/400000000000000000000000000000 : ℝ)*base69 + (1450982725876501/200000000000000000000000000000 : ℝ)*base71 + (2550748590970419/400000000000000000000000000000 : ℝ)*base74 + (3906127104076579/400000000000000000000000000000 : ℝ)*base75 + (1096800743676579/400000000000000000000000000000 : ℝ)*base77 + (3021248558323421/400000000000000000000000000000 : ℝ)*base80 + (187029331076579/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (104769/400000000000000000000 : ℝ)*base90 + (104769/400000000000000000000 : ℝ)*base92 + (104769/400000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1630_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35221777/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (889/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (23791/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1630_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1630_s1_0 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-821399067/5000000000 : ℝ)*x 0 + (344509681/625000000 : ℝ)*x 1 + (641493997/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (821399067/5000000000 : ℝ)^4839 ≤ (1011663071339/10000000000000 : ℝ)^3815 := by
    have hnat : (821399067 : ℕ)^4839*10000000000000^3815 ≤ 1011663071339^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      821399067 5000000000 1011663071339 10000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (344509681/625000000 : ℝ)^4839 ≤ (11744334913567/25000000000000 : ℝ)^3815 := by
    have hnat : (344509681 : ℕ)^4839*25000000000000^3815 ≤ 11744334913567^3815*625000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344509681 625000000 11744334913567 25000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (641493997/1250000000 : ℝ)^4839 ≤ (42906029622961/100000000000000 : ℝ)^3815 := by
    have hnat : (641493997 : ℕ)^4839*100000000000000^3815 ≤ 42906029622961^3815*1250000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641493997 1250000000 42906029622961 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-821399067/5000000000 : ℝ), (344509681/625000000 : ℝ), (641493997/1250000000 : ℝ)] ![(1011663071339/10000000000000 : ℝ), (11744334913567/25000000000000 : ℝ), (42906029622961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-821399067/5000000000 : ℝ)|^4839 ≤ (1011663071339/10000000000000 : ℝ)^3815
        have hw : |(-821399067/5000000000 : ℝ)|=(821399067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(344509681/625000000 : ℝ)|^4839 ≤ (11744334913567/25000000000000 : ℝ)^3815
        have hw : |(344509681/625000000 : ℝ)|=(344509681/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(641493997/1250000000 : ℝ)|^4839 ≤ (42906029622961/100000000000000 : ℝ)^3815
        have hw : |(641493997/1250000000 : ℝ)|=(641493997/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s1_1 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (53661547/100000000 : ℝ)*x 0 + (-920505151/5000000000 : ℝ)*x 1 + (1282987937/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53661547/100000000 : ℝ)^4839 ≤ (22702357920517/50000000000000 : ℝ)^3815 := by
    have hnat : (53661547 : ℕ)^4839*50000000000000^3815 ≤ 22702357920517^3815*100000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53661547 100000000 22702357920517 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (920505151/5000000000 : ℝ)^4839 ≤ (5844628471151/50000000000000 : ℝ)^3815 := by
    have hnat : (920505151 : ℕ)^4839*50000000000000^3815 ≤ 5844628471151^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      920505151 5000000000 5844628471151 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1282987937/2500000000 : ℝ)^4839 ≤ (42906027205099/100000000000000 : ℝ)^3815 := by
    have hnat : (1282987937 : ℕ)^4839*100000000000000^3815 ≤ 42906027205099^3815*2500000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1282987937 2500000000 42906027205099 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53661547/100000000 : ℝ), (-920505151/5000000000 : ℝ), (1282987937/2500000000 : ℝ)] ![(22702357920517/50000000000000 : ℝ), (5844628471151/50000000000000 : ℝ), (42906027205099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53661547/100000000 : ℝ)|^4839 ≤ (22702357920517/50000000000000 : ℝ)^3815
        have hw : |(53661547/100000000 : ℝ)|=(53661547/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-920505151/5000000000 : ℝ)|^4839 ≤ (5844628471151/50000000000000 : ℝ)^3815
        have hw : |(-920505151/5000000000 : ℝ)|=(920505151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1282987937/2500000000 : ℝ)|^4839 ≤ (42906027205099/100000000000000 : ℝ)^3815
        have hw : |(1282987937/2500000000 : ℝ)|=(1282987937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s1_2 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5366155423/10000000000 : ℝ)*x 0 + (1026390171/2000000000 : ℝ)*x 1 + (-920505257/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5366155423/10000000000 : ℝ)^4839 ≤ (9080944720119/20000000000000 : ℝ)^3815 := by
    have hnat : (5366155423 : ℕ)^4839*20000000000000^3815 ≤ 9080944720119^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5366155423 10000000000 9080944720119 20000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1026390171/2000000000 : ℝ)^4839 ≤ (1340813054223/3125000000000 : ℝ)^3815 := by
    have hnat : (1026390171 : ℕ)^4839*3125000000000^3815 ≤ 1340813054223^3815*2000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026390171 2000000000 1340813054223 3125000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (920505257/5000000000 : ℝ)^4839 ≤ (1461157331209/12500000000000 : ℝ)^3815 := by
    have hnat : (920505257 : ℕ)^4839*12500000000000^3815 ≤ 1461157331209^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      920505257 5000000000 1461157331209 12500000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5366155423/10000000000 : ℝ), (1026390171/2000000000 : ℝ), (-920505257/5000000000 : ℝ)] ![(9080944720119/20000000000000 : ℝ), (1340813054223/3125000000000 : ℝ), (1461157331209/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5366155423/10000000000 : ℝ)|^4839 ≤ (9080944720119/20000000000000 : ℝ)^3815
        have hw : |(5366155423/10000000000 : ℝ)|=(5366155423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1026390171/2000000000 : ℝ)|^4839 ≤ (1340813054223/3125000000000 : ℝ)^3815
        have hw : |(1026390171/2000000000 : ℝ)|=(1026390171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-920505257/5000000000 : ℝ)|^4839 ≤ (1461157331209/12500000000000 : ℝ)^3815
        have hw : |(-920505257/5000000000 : ℝ)|=(920505257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s1_3 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2093611297/5000000000 : ℝ)*x 0 + (3728205773/10000000000 : ℝ)*x 1 + (4687146927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2093611297/5000000000 : ℝ)^4839 ≤ (33147108411099/100000000000000 : ℝ)^3815 := by
    have hnat : (2093611297 : ℕ)^4839*100000000000000^3815 ≤ 33147108411099^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093611297 5000000000 33147108411099 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3728205773/10000000000 : ℝ)^4839 ≤ (28607794384563/100000000000000 : ℝ)^3815 := by
    have hnat : (3728205773 : ℕ)^4839*100000000000000^3815 ≤ 28607794384563^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3728205773 10000000000 28607794384563 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4687146927/10000000000 : ℝ)^4839 ≤ (4780637147629/12500000000000 : ℝ)^3815 := by
    have hnat : (4687146927 : ℕ)^4839*12500000000000^3815 ≤ 4780637147629^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4687146927 10000000000 4780637147629 12500000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2093611297/5000000000 : ℝ), (3728205773/10000000000 : ℝ), (4687146927/10000000000 : ℝ)] ![(33147108411099/100000000000000 : ℝ), (28607794384563/100000000000000 : ℝ), (4780637147629/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2093611297/5000000000 : ℝ)|^4839 ≤ (33147108411099/100000000000000 : ℝ)^3815
        have hw : |(2093611297/5000000000 : ℝ)|=(2093611297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3728205773/10000000000 : ℝ)|^4839 ≤ (28607794384563/100000000000000 : ℝ)^3815
        have hw : |(3728205773/10000000000 : ℝ)|=(3728205773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4687146927/10000000000 : ℝ)|^4839 ≤ (4780637147629/12500000000000 : ℝ)^3815
        have hw : |(4687146927/10000000000 : ℝ)|=(4687146927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s1_4 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-164298409/1000000000 : ℝ)*x 0 + (2567970283/5000000000 : ℝ)*x 1 + (2754053457/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164298409/1000000000 : ℝ)^4839 ≤ (10118083258301/100000000000000 : ℝ)^3815 := by
    have hnat : (164298409 : ℕ)^4839*100000000000000^3815 ≤ 10118083258301^3815*1000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164298409 1000000000 10118083258301 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2567970283/5000000000 : ℝ)^4839 ≤ (42948331682229/100000000000000 : ℝ)^3815 := by
    have hnat : (2567970283 : ℕ)^4839*100000000000000^3815 ≤ 42948331682229^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2567970283 5000000000 42948331682229 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2754053457/5000000000 : ℝ)^4839 ≤ (46933585041443/100000000000000 : ℝ)^3815 := by
    have hnat : (2754053457 : ℕ)^4839*100000000000000^3815 ≤ 46933585041443^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2754053457 5000000000 46933585041443 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-164298409/1000000000 : ℝ), (2567970283/5000000000 : ℝ), (2754053457/5000000000 : ℝ)] ![(10118083258301/100000000000000 : ℝ), (42948331682229/100000000000000 : ℝ), (46933585041443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-164298409/1000000000 : ℝ)|^4839 ≤ (10118083258301/100000000000000 : ℝ)^3815
        have hw : |(-164298409/1000000000 : ℝ)|=(164298409/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2567970283/5000000000 : ℝ)|^4839 ≤ (42948331682229/100000000000000 : ℝ)^3815
        have hw : |(2567970283/5000000000 : ℝ)|=(2567970283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2754053457/5000000000 : ℝ)|^4839 ≤ (46933585041443/100000000000000 : ℝ)^3815
        have hw : |(2754053457/5000000000 : ℝ)|=(2754053457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s1_5 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (526472991/1000000000 : ℝ)*x 0 + (-292970861/2000000000 : ℝ)*x 1 + (5508107269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526472991/1000000000 : ℝ)^4839 ≤ (5539869180871/12500000000000 : ℝ)^3815 := by
    have hnat : (526472991 : ℕ)^4839*12500000000000^3815 ≤ 5539869180871^3815*1000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526472991 1000000000 5539869180871 12500000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (292970861/2000000000 : ℝ)^4839 ≤ (8747457665251/100000000000000 : ℝ)^3815 := by
    have hnat : (292970861 : ℕ)^4839*100000000000000^3815 ≤ 8747457665251^3815*2000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      292970861 2000000000 8747457665251 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5508107269/10000000000 : ℝ)^4839 ≤ (23466794439129/50000000000000 : ℝ)^3815 := by
    have hnat : (5508107269 : ℕ)^4839*50000000000000^3815 ≤ 23466794439129^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5508107269 10000000000 23466794439129 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(526472991/1000000000 : ℝ), (-292970861/2000000000 : ℝ), (5508107269/10000000000 : ℝ)] ![(5539869180871/12500000000000 : ℝ), (8747457665251/100000000000000 : ℝ), (23466794439129/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(526472991/1000000000 : ℝ)|^4839 ≤ (5539869180871/12500000000000 : ℝ)^3815
        have hw : |(526472991/1000000000 : ℝ)|=(526472991/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-292970861/2000000000 : ℝ)|^4839 ≤ (8747457665251/100000000000000 : ℝ)^3815
        have hw : |(-292970861/2000000000 : ℝ)|=(292970861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5508107269/10000000000 : ℝ)|^4839 ≤ (23466794439129/50000000000000 : ℝ)^3815
        have hw : |(5508107269/10000000000 : ℝ)|=(5508107269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s1_6 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2632364623/5000000000 : ℝ)*x 0 + (5508107511/10000000000 : ℝ)*x 1 + (-292970979/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2632364623/5000000000 : ℝ)^4839 ≤ (11079736589257/25000000000000 : ℝ)^3815 := by
    have hnat : (2632364623 : ℕ)^4839*25000000000000^3815 ≤ 11079736589257^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632364623 5000000000 11079736589257 25000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5508107511/10000000000 : ℝ)^4839 ≤ (2933349468361/6250000000000 : ℝ)^3815 := by
    have hnat : (5508107511 : ℕ)^4839*6250000000000^3815 ≤ 2933349468361^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5508107511 10000000000 2933349468361 6250000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (292970979/2000000000 : ℝ)^4839 ≤ (174949242683/2000000000000 : ℝ)^3815 := by
    have hnat : (292970979 : ℕ)^4839*2000000000000^3815 ≤ 174949242683^3815*2000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      292970979 2000000000 174949242683 2000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2632364623/5000000000 : ℝ), (5508107511/10000000000 : ℝ), (-292970979/2000000000 : ℝ)] ![(11079736589257/25000000000000 : ℝ), (2933349468361/6250000000000 : ℝ), (174949242683/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2632364623/5000000000 : ℝ)|^4839 ≤ (11079736589257/25000000000000 : ℝ)^3815
        have hw : |(2632364623/5000000000 : ℝ)|=(2632364623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5508107511/10000000000 : ℝ)|^4839 ≤ (2933349468361/6250000000000 : ℝ)^3815
        have hw : |(5508107511/10000000000 : ℝ)|=(5508107511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-292970979/2000000000 : ℝ)|^4839 ≤ (174949242683/2000000000000 : ℝ)^3815
        have hw : |(-292970979/2000000000 : ℝ)|=(292970979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s1_7 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2093844371/5000000000 : ℝ)*x 0 + (4677087781/10000000000 : ℝ)*x 1 + (3738414583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2093844371/5000000000 : ℝ)^4839 ≤ (33151789113111/100000000000000 : ℝ)^3815 := by
    have hnat : (2093844371 : ℕ)^4839*100000000000000^3815 ≤ 33151789113111^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093844371 5000000000 33151789113111 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4677087781/10000000000 : ℝ)^4839 ≤ (19070508957349/50000000000000 : ℝ)^3815 := by
    have hnat : (4677087781 : ℕ)^4839*50000000000000^3815 ≤ 19070508957349^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4677087781 10000000000 19070508957349 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3738414583/10000000000 : ℝ)^4839 ≤ (5741438592311/20000000000000 : ℝ)^3815 := by
    have hnat : (3738414583 : ℕ)^4839*20000000000000^3815 ≤ 5741438592311^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3738414583 10000000000 5741438592311 20000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2093844371/5000000000 : ℝ), (4677087781/10000000000 : ℝ), (3738414583/10000000000 : ℝ)] ![(33151789113111/100000000000000 : ℝ), (19070508957349/50000000000000 : ℝ), (5741438592311/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2093844371/5000000000 : ℝ)|^4839 ≤ (33151789113111/100000000000000 : ℝ)^3815
        have hw : |(2093844371/5000000000 : ℝ)|=(2093844371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4677087781/10000000000 : ℝ)|^4839 ≤ (19070508957349/50000000000000 : ℝ)^3815
        have hw : |(4677087781/10000000000 : ℝ)|=(4677087781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3738414583/10000000000 : ℝ)|^4839 ≤ (5741438592311/20000000000000 : ℝ)^3815
        have hw : |(3738414583/10000000000 : ℝ)|=(3738414583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1630_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35221777/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23791/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (889/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (4733/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17533/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (23791/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (889/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (23791/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (889/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (23791/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (889/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (23791/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (889/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (23791/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (889/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (23791/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (889/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (889/20000 : ℝ) ^ (4835/1024 : ℝ) ≤ (20637333559299/50000000000000000000 : ℝ) := by
    have hpowers : (889/20000 : ℝ)^4835 ≤ (20637333559299/50000000000000000000 : ℝ)^1024 := by
      have hnat : (889 : ℕ)^4835*50000000000000000000^1024 ≤ 20637333559299^1024*20000^4835 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        889 20000 20637333559299 50000000000000000000 4835 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (889/20000 : ℝ)) (X := (20637333559299/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4835 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (23791/100000 : ℝ) ^ (4835/1024 : ℝ) ≤ (5683168103807787/5000000000000000000 : ℝ) := by
    have hpowers : (23791/100000 : ℝ)^4835 ≤ (5683168103807787/5000000000000000000 : ℝ)^1024 := by
      have hnat : (23791 : ℕ)^4835*5000000000000000000^1024 ≤ 5683168103807787^1024*100000^4835 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23791 100000 5683168103807787 5000000000000000000 4835 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (23791/100000 : ℝ)) (X := (5683168103807787/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4835 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000020637333559299/25000000000000000000 : ℝ) ≤ (5000000874151921/5000000000000000 : ℝ) ^ (4835/1024 : ℝ) := by
    have hpowers : (25000020637333559299/25000000000000000000 : ℝ)^1024 ≤ (5000000874151921/5000000000000000 : ℝ)^4835 := by
      have hnat : (25000020637333559299 : ℕ)^1024*5000000000000000^4835 ≤ 5000000874151921^4835*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000020637333559299 25000000000000000000 5000000874151921 5000000000000000 1024 4835 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000874151921/5000000000000000 : ℝ)) (X := (25000020637333559299/25000000000000000000 : ℝ)) (by norm_num) 4835 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50056852318371637169/50000000000000000000 : ℝ) ≤ (10002407061170631/10000000000000000 : ℝ) ^ (4835/1024 : ℝ) := by
    have hpowers : (50056852318371637169/50000000000000000000 : ℝ)^1024 ≤ (10002407061170631/10000000000000000 : ℝ)^4835 := by
      have hnat : (50056852318371637169 : ℕ)^1024*10000000000000000^4835 ≤ 10002407061170631^4835*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50056852318371637169 50000000000000000000 10002407061170631 10000000000000000 1024 4835 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002407061170631/10000000000000000 : ℝ)) (X := (50056852318371637169/50000000000000000000 : ℝ)) (by norm_num) 4835 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2505683168103807787/2500000000000000000 : ℝ) ≤ (500240618701871/500000000000000 : ℝ) ^ (4835/1024 : ℝ) := by
    have hpowers : (2505683168103807787/2500000000000000000 : ℝ)^1024 ≤ (500240618701871/500000000000000 : ℝ)^4835 := by
      have hnat : (2505683168103807787 : ℕ)^1024*500000000000000^4835 ≤ 500240618701871^4835*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2505683168103807787 2500000000000000000 500240618701871 500000000000000 1024 4835 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500240618701871/500000000000000 : ℝ)) (X := (2505683168103807787/2500000000000000000 : ℝ)) (by norm_num) 4835 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(20637333559299/50000000000000000000 : ℝ) ≤ ((96719325295650186561/96730000000000000000 : ℝ)+2*(2405312866789/1934600000000000 : ℝ)*(889/20000 : ℝ))^(4835/1024 : ℝ) := by
    rw [show (96719325295650186561/96730000000000000000 : ℝ)+2*(2405312866789/1934600000000000 : ℝ)*(889/20000 : ℝ)=(5000000874151921/5000000000000000 : ℝ) by norm_num, show 1+2*(20637333559299/50000000000000000000 : ℝ)=(25000020637333559299/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5683168103807787/5000000000000000000 : ℝ)+(20637333559299/50000000000000000000 : ℝ) ≤ ((96719325295650186561/96730000000000000000 : ℝ)+(2405312866789/1934600000000000 : ℝ)*((23791/100000 : ℝ)+(889/20000 : ℝ)))^(4835/1024 : ℝ) := by
    rw [show (96719325295650186561/96730000000000000000 : ℝ)+(2405312866789/1934600000000000 : ℝ)*((23791/100000 : ℝ)+(889/20000 : ℝ))=(10002407061170631/10000000000000000 : ℝ) by norm_num, show 1+(5683168103807787/5000000000000000000 : ℝ)+(20637333559299/50000000000000000000 : ℝ)=(50056852318371637169/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5683168103807787/5000000000000000000 : ℝ) ≤ ((96719325295650186561/96730000000000000000 : ℝ)+2*(2405312866789/1934600000000000 : ℝ)*(23791/100000 : ℝ))^(4835/1024 : ℝ) := by
    rw [show (96719325295650186561/96730000000000000000 : ℝ)+2*(2405312866789/1934600000000000 : ℝ)*(23791/100000 : ℝ)=(500240618701871/500000000000000 : ℝ) by norm_num, show 1+2*(5683168103807787/5000000000000000000 : ℝ)=(2505683168103807787/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (96719325295650186561/96730000000000000000 : ℝ)*(X 1 0+X 2 0)+(2405312866789/1934600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4835/1024 : ℝ)) (lo := (889/20000 : ℝ)) (hi := (23791/100000 : ℝ)) (c := (96719325295650186561/96730000000000000000 : ℝ)) (alpha := (2405312866789/1934600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (96719325295650186561/96730000000000000000 : ℝ)*(X 0 1+X 2 1)+(2405312866789/1934600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4835/1024 : ℝ)) (lo := (889/20000 : ℝ)) (hi := (23791/100000 : ℝ)) (c := (96719325295650186561/96730000000000000000 : ℝ)) (alpha := (2405312866789/1934600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (96719325295650186561/96730000000000000000 : ℝ)*(X 0 2+X 1 2)+(2405312866789/1934600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4835/1024 : ℝ)) (lo := (889/20000 : ℝ)) (hi := (23791/100000 : ℝ)) (c := (96719325295650186561/96730000000000000000 : ℝ)) (alpha := (2405312866789/1934600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-821399067/5000000000 : ℝ)*X 0 0+(344509681/625000000 : ℝ)*X 0 1+(641493997/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((53661547/100000000 : ℝ)*X 1 0+(-920505151/5000000000 : ℝ)*X 1 1+(1282987937/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5366155423/10000000000 : ℝ)*X 2 0+(1026390171/2000000000 : ℝ)*X 2 1+(-920505257/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2093611297/5000000000 : ℝ)*X 0 0+(3728205773/10000000000 : ℝ)*X 0 1+(4687146927/10000000000 : ℝ)*X 0 2+(2093611297/5000000000 : ℝ)*X 1 0+(3728205773/10000000000 : ℝ)*X 1 1+(4687146927/10000000000 : ℝ)*X 1 2+(2093611297/5000000000 : ℝ)*X 2 0+(3728205773/10000000000 : ℝ)*X 2 1+(4687146927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-164298409/1000000000 : ℝ)*X 0 0+(2567970283/5000000000 : ℝ)*X 0 1+(2754053457/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((526472991/1000000000 : ℝ)*X 1 0+(-292970861/2000000000 : ℝ)*X 1 1+(5508107269/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2632364623/5000000000 : ℝ)*X 2 0+(5508107511/10000000000 : ℝ)*X 2 1+(-292970979/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2093844371/5000000000 : ℝ)*X 0 0+(4677087781/10000000000 : ℝ)*X 0 1+(3738414583/10000000000 : ℝ)*X 0 2+(2093844371/5000000000 : ℝ)*X 1 0+(4677087781/10000000000 : ℝ)*X 1 1+(3738414583/10000000000 : ℝ)*X 1 2+(2093844371/5000000000 : ℝ)*X 2 0+(4677087781/10000000000 : ℝ)*X 2 1+(3738414583/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (364799837978048008399875729/120912500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (218307413/100000000000000 : ℝ)*(base1) + (353328983/100000000000000 : ℝ)*(base19) + (884044207/100000000000000 : ℝ)*(base23) + (314701/5000000000000 : ℝ)*(lower2) + (20184519/20000000000000 : ℝ)*(lower4) + (20082839/25000000000000 : ℝ)*(upper5) + (1836495512981479/100000000000000 : ℝ)*(major0) + (1836495512981479/100000000000000 : ℝ)*(major1) + (45912387824537/2500000000000 : ℝ)*(major2) + (657543234735223/25000000000000 : ℝ)*(sp0) + (164385772956531/6250000000000 : ℝ)*(sp1) + (328771479573659/12500000000000 : ℝ)*(sp2) + (208563523568253/20000000000000 : ℝ)*(sp3) + (73722449/20000000000000 : ℝ)*(sp7) + (260704551190231/25000000000000 : ℝ)*(f.failure) + (2630172720633479/100000000000000 : ℝ)*(f.sum) + (1265283043596469/193460000000000000000000000000 : ℝ)*base66 + (19909806901067703719/9673000000000000000000000000000000 : ℝ)*base67 + (2309632927604961007/241825000000000000000000000000000 : ℝ)*base69 + (82966513816126296281/9673000000000000000000000000000000 : ℝ)*base72 + (1379181335091571/193460000000000000000000000000 : ℝ)*base73 + (2733103224805761007/241825000000000000000000000000000 : ℝ)*base75 + (27224148709553746281/9673000000000000000000000000000000 : ℝ)*base78 + (40762343224984253719/9673000000000000000000000000000000 : ℝ)*base79 + (275629272581071/96730000000000000000000000000 : ℝ)*base81 + (5860487/500000000000000000000 : ℝ)*base89 + (5860487/500000000000000000000 : ℝ)*base91 + (860487/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11782330018254443514281149203/1209125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (379682087/20000000000000 : ℝ)*(base19) + (1604853941/100000000000000 : ℝ)*(base23) + (29308429/100000000000000 : ℝ)*(upper2) + (399961311/100000000000000 : ℝ)*(upper3) + (358057/390625000000 : ℝ)*(upper5) + (469037331013441/25000000000000 : ℝ)*(major0) + (469037331013441/25000000000000 : ℝ)*(major1) + (469037331013441/25000000000000 : ℝ)*(major2) + (14573001473/100000000000000 : ℝ)*(sp1) + (2807216821/20000000000000 : ℝ)*(sp2) + (1343481737155651/50000000000000 : ℝ)*(sp4) + (2686947002899393/100000000000000 : ℝ)*(sp5) + (335868479171657/12500000000000 : ℝ)*(sp6) + (532667424489617/50000000000000 : ℝ)*(sp7) + (532667424489617/50000000000000 : ℝ)*(f.failure) + (1343481737155651/50000000000000 : ℝ)*(f.sum) + (37663366042189/24182500000000000000000000000 : ℝ)*base65 + (691614582523483599/2418250000000000000000000000000000 : ℝ)*base68 + (1351542345566483599/2418250000000000000000000000000000 : ℝ)*base70 + (11827219084412516401/2418250000000000000000000000000000 : ℝ)*base71 + (116761133277797/48365000000000000000000000000 : ℝ)*base74 + (23572464459736266401/2418250000000000000000000000000000 : ℝ)*base75 + (103165687550733599/2418250000000000000000000000000000 : ℝ)*base78 + (16392607297150233599/2418250000000000000000000000000000 : ℝ)*base80 + (69281391700141/24182500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (11210591/1000000000000000000000 : ℝ)*base90 + (11210591/1000000000000000000000 : ℝ)*base92 + (11210591/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1630_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35221777/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23791/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (889/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4733/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17533/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1630_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1630_s2_0 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-330837579/2000000000 : ℝ)*x 0 + (2729268787/5000000000 : ℝ)*x 1 + (5178083553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330837579/2000000000 : ℝ)^4839 ≤ (2041136007193/20000000000000 : ℝ)^3815 := by
    have hnat : (330837579 : ℕ)^4839*20000000000000^3815 ≤ 2041136007193^3815*2000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330837579 2000000000 2041136007193 20000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2729268787/5000000000 : ℝ)^4839 ≤ (1449952864353/3125000000000 : ℝ)^3815 := by
    have hnat : (2729268787 : ℕ)^4839*3125000000000^3815 ≤ 1449952864353^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729268787 5000000000 1449952864353 3125000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5178083553/10000000000 : ℝ)^4839 ≤ (43395828290957/100000000000000 : ℝ)^3815 := by
    have hnat : (5178083553 : ℕ)^4839*100000000000000^3815 ≤ 43395828290957^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178083553 10000000000 43395828290957 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-330837579/2000000000 : ℝ), (2729268787/5000000000 : ℝ), (5178083553/10000000000 : ℝ)] ![(2041136007193/20000000000000 : ℝ), (1449952864353/3125000000000 : ℝ), (43395828290957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-330837579/2000000000 : ℝ)|^4839 ≤ (2041136007193/20000000000000 : ℝ)^3815
        have hw : |(-330837579/2000000000 : ℝ)|=(330837579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2729268787/5000000000 : ℝ)|^4839 ≤ (1449952864353/3125000000000 : ℝ)^3815
        have hw : |(2729268787/5000000000 : ℝ)|=(2729268787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5178083553/10000000000 : ℝ)|^4839 ≤ (43395828290957/100000000000000 : ℝ)^3815
        have hw : |(5178083553/10000000000 : ℝ)|=(5178083553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s2_1 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352067109/10000000000 : ℝ)*x 0 + (-1798829213/10000000000 : ℝ)*x 1 + (2589041797/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352067109/10000000000 : ℝ)^4839 ≤ (22626787393297/50000000000000 : ℝ)^3815 := by
    have hnat : (5352067109 : ℕ)^4839*50000000000000^3815 ≤ 22626787393297^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352067109 10000000000 22626787393297 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1798829213/10000000000 : ℝ)^4839 ≤ (2270119294549/20000000000000 : ℝ)^3815 := by
    have hnat : (1798829213 : ℕ)^4839*20000000000000^3815 ≤ 2270119294549^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1798829213 10000000000 2270119294549 20000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2589041797/5000000000 : ℝ)^4839 ≤ (21697914363397/50000000000000 : ℝ)^3815 := by
    have hnat : (2589041797 : ℕ)^4839*50000000000000^3815 ≤ 21697914363397^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589041797 5000000000 21697914363397 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352067109/10000000000 : ℝ), (-1798829213/10000000000 : ℝ), (2589041797/5000000000 : ℝ)] ![(22626787393297/50000000000000 : ℝ), (2270119294549/20000000000000 : ℝ), (21697914363397/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352067109/10000000000 : ℝ)|^4839 ≤ (22626787393297/50000000000000 : ℝ)^3815
        have hw : |(5352067109/10000000000 : ℝ)|=(5352067109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1798829213/10000000000 : ℝ)|^4839 ≤ (2270119294549/20000000000000 : ℝ)^3815
        have hw : |(-1798829213/10000000000 : ℝ)|=(1798829213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2589041797/5000000000 : ℝ)|^4839 ≤ (21697914363397/50000000000000 : ℝ)^3815
        have hw : |(2589041797/5000000000 : ℝ)|=(2589041797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s2_2 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338016789/2500000000 : ℝ)*x 0 + (5178083483/10000000000 : ℝ)*x 1 + (-899414649/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338016789/2500000000 : ℝ)^4839 ≤ (45253575290663/100000000000000 : ℝ)^3815 := by
    have hnat : (1338016789 : ℕ)^4839*100000000000000^3815 ≤ 45253575290663^3815*2500000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338016789 2500000000 45253575290663 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5178083483/10000000000 : ℝ)^4839 ≤ (21697913773423/50000000000000 : ℝ)^3815 := by
    have hnat : (5178083483 : ℕ)^4839*50000000000000^3815 ≤ 21697913773423^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178083483 10000000000 21697913773423 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (899414649/5000000000 : ℝ)^4839 ≤ (5675298576529/50000000000000 : ℝ)^3815 := by
    have hnat : (899414649 : ℕ)^4839*50000000000000^3815 ≤ 5675298576529^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899414649 5000000000 5675298576529 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338016789/2500000000 : ℝ), (5178083483/10000000000 : ℝ), (-899414649/5000000000 : ℝ)] ![(45253575290663/100000000000000 : ℝ), (21697913773423/50000000000000 : ℝ), (5675298576529/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338016789/2500000000 : ℝ)|^4839 ≤ (45253575290663/100000000000000 : ℝ)^3815
        have hw : |(1338016789/2500000000 : ℝ)|=(1338016789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5178083483/10000000000 : ℝ)|^4839 ≤ (21697913773423/50000000000000 : ℝ)^3815
        have hw : |(5178083483/10000000000 : ℝ)|=(5178083483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-899414649/5000000000 : ℝ)|^4839 ≤ (5675298576529/50000000000000 : ℝ)^3815
        have hw : |(-899414649/5000000000 : ℝ)|=(899414649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s2_3 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (419567177/1000000000 : ℝ)*x 0 + (3853127979/10000000000 : ℝ)*x 1 + (2280241449/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419567177/1000000000 : ℝ)^4839 ≤ (16615985138231/50000000000000 : ℝ)^3815 := by
    have hnat : (419567177 : ℕ)^4839*50000000000000^3815 ≤ 16615985138231^3815*1000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419567177 1000000000 16615985138231 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3853127979/10000000000 : ℝ)^4839 ≤ (29829082622757/100000000000000 : ℝ)^3815 := by
    have hnat : (3853127979 : ℕ)^4839*100000000000000^3815 ≤ 29829082622757^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3853127979 10000000000 29829082622757 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2280241449/5000000000 : ℝ)^4839 ≤ (9234736770279/25000000000000 : ℝ)^3815 := by
    have hnat : (2280241449 : ℕ)^4839*25000000000000^3815 ≤ 9234736770279^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2280241449 5000000000 9234736770279 25000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(419567177/1000000000 : ℝ), (3853127979/10000000000 : ℝ), (2280241449/5000000000 : ℝ)] ![(16615985138231/50000000000000 : ℝ), (29829082622757/100000000000000 : ℝ), (9234736770279/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(419567177/1000000000 : ℝ)|^4839 ≤ (16615985138231/50000000000000 : ℝ)^3815
        have hw : |(419567177/1000000000 : ℝ)|=(419567177/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3853127979/10000000000 : ℝ)|^4839 ≤ (29829082622757/100000000000000 : ℝ)^3815
        have hw : |(3853127979/10000000000 : ℝ)|=(3853127979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2280241449/5000000000 : ℝ)|^4839 ≤ (9234736770279/25000000000000 : ℝ)^3815
        have hw : |(2280241449/5000000000 : ℝ)|=(2280241449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s2_4 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-330852409/2000000000 : ℝ)*x 0 + (518026071/1000000000 : ℝ)*x 1 + (5456336963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330852409/2000000000 : ℝ)^4839 ≤ (1275782538553/12500000000000 : ℝ)^3815 := by
    have hnat : (330852409 : ℕ)^4839*12500000000000^3815 ≤ 1275782538553^3815*2000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330852409 2000000000 1275782538553 12500000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (518026071/1000000000 : ℝ)^4839 ≤ (43418973135041/100000000000000 : ℝ)^3815 := by
    have hnat : (518026071 : ℕ)^4839*100000000000000^3815 ≤ 43418973135041^3815*1000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518026071 1000000000 43418973135041 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5456336963/10000000000 : ℝ)^4839 ≤ (23187383269667/50000000000000 : ℝ)^3815 := by
    have hnat : (5456336963 : ℕ)^4839*50000000000000^3815 ≤ 23187383269667^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456336963 10000000000 23187383269667 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-330852409/2000000000 : ℝ), (518026071/1000000000 : ℝ), (5456336963/10000000000 : ℝ)] ![(1275782538553/12500000000000 : ℝ), (43418973135041/100000000000000 : ℝ), (23187383269667/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-330852409/2000000000 : ℝ)|^4839 ≤ (1275782538553/12500000000000 : ℝ)^3815
        have hw : |(-330852409/2000000000 : ℝ)|=(330852409/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(518026071/1000000000 : ℝ)|^4839 ≤ (43418973135041/100000000000000 : ℝ)^3815
        have hw : |(518026071/1000000000 : ℝ)|=(518026071/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5456336963/10000000000 : ℝ)|^4839 ≤ (23187383269667/50000000000000 : ℝ)^3815
        have hw : |(5456336963/10000000000 : ℝ)|=(5456336963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s2_5 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638667219/5000000000 : ℝ)*x 0 + (-1520575731/10000000000 : ℝ)*x 1 + (545633707/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638667219/5000000000 : ℝ)^4839 ≤ (22226791516041/50000000000000 : ℝ)^3815 := by
    have hnat : (2638667219 : ℕ)^4839*50000000000000^3815 ≤ 22226791516041^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638667219 5000000000 22226791516041 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1520575731/10000000000 : ℝ)^4839 ≤ (1146456157469/12500000000000 : ℝ)^3815 := by
    have hnat : (1520575731 : ℕ)^4839*12500000000000^3815 ≤ 1146456157469^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1520575731 10000000000 1146456157469 12500000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (545633707/1000000000 : ℝ)^4839 ≤ (9274953538571/20000000000000 : ℝ)^3815 := by
    have hnat : (545633707 : ℕ)^4839*20000000000000^3815 ≤ 9274953538571^3815*1000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545633707 1000000000 9274953538571 20000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638667219/5000000000 : ℝ), (-1520575731/10000000000 : ℝ), (545633707/1000000000 : ℝ)] ![(22226791516041/50000000000000 : ℝ), (1146456157469/12500000000000 : ℝ), (9274953538571/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638667219/5000000000 : ℝ)|^4839 ≤ (22226791516041/50000000000000 : ℝ)^3815
        have hw : |(2638667219/5000000000 : ℝ)|=(2638667219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1520575731/10000000000 : ℝ)|^4839 ≤ (1146456157469/12500000000000 : ℝ)^3815
        have hw : |(-1520575731/10000000000 : ℝ)|=(1520575731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(545633707/1000000000 : ℝ)|^4839 ≤ (9274953538571/20000000000000 : ℝ)^3815
        have hw : |(545633707/1000000000 : ℝ)|=(545633707/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s2_6 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527733539/1000000000 : ℝ)*x 0 + (5456335941/10000000000 : ℝ)*x 1 + (-190071999/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527733539/1000000000 : ℝ)^4839 ≤ (5556699150463/12500000000000 : ℝ)^3815 := by
    have hnat : (527733539 : ℕ)^4839*12500000000000^3815 ≤ 5556699150463^3815*1000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527733539 1000000000 5556699150463 12500000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5456335941/10000000000 : ℝ)^4839 ≤ (23187377760797/50000000000000 : ℝ)^3815 := by
    have hnat : (5456335941 : ℕ)^4839*50000000000000^3815 ≤ 23187377760797^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456335941 10000000000 23187377760797 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (190071999/1250000000 : ℝ)^4839 ≤ (4585825628291/50000000000000 : ℝ)^3815 := by
    have hnat : (190071999 : ℕ)^4839*50000000000000^3815 ≤ 4585825628291^3815*1250000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190071999 1250000000 4585825628291 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527733539/1000000000 : ℝ), (5456335941/10000000000 : ℝ), (-190071999/1250000000 : ℝ)] ![(5556699150463/12500000000000 : ℝ), (23187377760797/50000000000000 : ℝ), (4585825628291/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527733539/1000000000 : ℝ)|^4839 ≤ (5556699150463/12500000000000 : ℝ)^3815
        have hw : |(527733539/1000000000 : ℝ)|=(527733539/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5456335941/10000000000 : ℝ)|^4839 ≤ (23187377760797/50000000000000 : ℝ)^3815
        have hw : |(5456335941/10000000000 : ℝ)|=(5456335941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-190071999/1250000000 : ℝ)|^4839 ≤ (4585825628291/50000000000000 : ℝ)^3815
        have hw : |(-190071999/1250000000 : ℝ)|=(190071999/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s2_7 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2097929711/5000000000 : ℝ)*x 0 + (910998681/2000000000 : ℝ)*x 1 + (964669381/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2097929711/5000000000 : ℝ)^4839 ≤ (166169277687/500000000000 : ℝ)^3815 := by
    have hnat : (2097929711 : ℕ)^4839*500000000000^3815 ≤ 166169277687^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097929711 5000000000 166169277687 500000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (910998681/2000000000 : ℝ)^4839 ≤ (7376511553427/20000000000000 : ℝ)^3815 := by
    have hnat : (910998681 : ℕ)^4839*20000000000000^3815 ≤ 7376511553427^3815*2000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      910998681 2000000000 7376511553427 20000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (964669381/2500000000 : ℝ)^4839 ≤ (14941793339829/50000000000000 : ℝ)^3815 := by
    have hnat : (964669381 : ℕ)^4839*50000000000000^3815 ≤ 14941793339829^3815*2500000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      964669381 2500000000 14941793339829 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2097929711/5000000000 : ℝ), (910998681/2000000000 : ℝ), (964669381/2500000000 : ℝ)] ![(166169277687/500000000000 : ℝ), (7376511553427/20000000000000 : ℝ), (14941793339829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2097929711/5000000000 : ℝ)|^4839 ≤ (166169277687/500000000000 : ℝ)^3815
        have hw : |(2097929711/5000000000 : ℝ)|=(2097929711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(910998681/2000000000 : ℝ)|^4839 ≤ (7376511553427/20000000000000 : ℝ)^3815
        have hw : |(910998681/2000000000 : ℝ)|=(910998681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(964669381/2500000000 : ℝ)|^4839 ≤ (14941793339829/50000000000000 : ℝ)^3815
        have hw : |(964669381/2500000000 : ℝ)|=(964669381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1630_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35221777/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17533/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4733/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5231/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3283/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17533/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4733/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17533/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4733/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17533/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4733/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17533/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4733/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17533/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4733/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17533/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4733/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4733/50000 : ℝ) ^ (4835/1024 : ℝ) ≤ (732413203044643/50000000000000000000 : ℝ) := by
    have hpowers : (4733/50000 : ℝ)^4835 ≤ (732413203044643/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4733 : ℕ)^4835*50000000000000000000^1024 ≤ 732413203044643^1024*50000^4835 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4733 50000 732413203044643 50000000000000000000 4835 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4733/50000 : ℝ)) (X := (732413203044643/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4835 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17533/100000 : ℝ) ^ (4835/1024 : ℝ) ≤ (5379740524313573/20000000000000000000 : ℝ) := by
    have hpowers : (17533/100000 : ℝ)^4835 ≤ (5379740524313573/20000000000000000000 : ℝ)^1024 := by
      have hnat : (17533 : ℕ)^4835*20000000000000000000^1024 ≤ 5379740524313573^1024*100000^4835 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17533 100000 5379740524313573 20000000000000000000 4835 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17533/100000 : ℝ)) (X := (5379740524313573/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4835 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000732413203044643/25000000000000000000 : ℝ) ≤ (10000062046118779/10000000000000000 : ℝ) ^ (4835/1024 : ℝ) := by
    have hpowers : (25000732413203044643/25000000000000000000 : ℝ)^1024 ≤ (10000062046118779/10000000000000000 : ℝ)^4835 := by
      have hnat : (25000732413203044643 : ℕ)^1024*10000000000000000^4835 ≤ 10000062046118779^4835*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000732413203044643 25000000000000000000 10000062046118779 10000000000000000 1024 4835 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000062046118779/10000000000000000 : ℝ)) (X := (25000732413203044643/25000000000000000000 : ℝ)) (by norm_num) 4835 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100028363529027657151/100000000000000000000 : ℝ) ≤ (400024025652651/400000000000000 : ℝ) ^ (4835/1024 : ℝ) := by
    have hpowers : (100028363529027657151/100000000000000000000 : ℝ)^1024 ≤ (400024025652651/400000000000000 : ℝ)^4835 := by
      have hnat : (100028363529027657151 : ℕ)^1024*400000000000000^4835 ≤ 400024025652651^4835*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100028363529027657151 100000000000000000000 400024025652651 400000000000000 1024 4835 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400024025652651/400000000000000 : ℝ)) (X := (100028363529027657151/100000000000000000000 : ℝ)) (by norm_num) 4835 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005379740524313573/10000000000000000000 : ℝ) ≤ (10001139236513771/10000000000000000 : ℝ) ^ (4835/1024 : ℝ) := by
    have hpowers : (10005379740524313573/10000000000000000000 : ℝ)^1024 ≤ (10001139236513771/10000000000000000 : ℝ)^4835 := by
      have hnat : (10005379740524313573 : ℕ)^1024*10000000000000000^4835 ≤ 10001139236513771^4835*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005379740524313573 10000000000000000000 10001139236513771 10000000000000000 1024 4835 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001139236513771/10000000000000000 : ℝ)) (X := (10005379740524313573/10000000000000000000 : ℝ)) (by norm_num) 4835 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(732413203044643/50000000000000000000 : ℝ) ≤ ((80660303841761195921/80670000000000000000 : ℝ)+2*(67324399687/100837500000000 : ℝ)*(4733/50000 : ℝ))^(4835/1024 : ℝ) := by
    rw [show (80660303841761195921/80670000000000000000 : ℝ)+2*(67324399687/100837500000000 : ℝ)*(4733/50000 : ℝ)=(10000062046118779/10000000000000000 : ℝ) by norm_num, show 1+2*(732413203044643/50000000000000000000 : ℝ)=(25000732413203044643/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5379740524313573/20000000000000000000 : ℝ)+(732413203044643/50000000000000000000 : ℝ) ≤ ((80660303841761195921/80670000000000000000 : ℝ)+(67324399687/100837500000000 : ℝ)*((17533/100000 : ℝ)+(4733/50000 : ℝ)))^(4835/1024 : ℝ) := by
    rw [show (80660303841761195921/80670000000000000000 : ℝ)+(67324399687/100837500000000 : ℝ)*((17533/100000 : ℝ)+(4733/50000 : ℝ))=(400024025652651/400000000000000 : ℝ) by norm_num, show 1+(5379740524313573/20000000000000000000 : ℝ)+(732413203044643/50000000000000000000 : ℝ)=(100028363529027657151/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5379740524313573/20000000000000000000 : ℝ) ≤ ((80660303841761195921/80670000000000000000 : ℝ)+2*(67324399687/100837500000000 : ℝ)*(17533/100000 : ℝ))^(4835/1024 : ℝ) := by
    rw [show (80660303841761195921/80670000000000000000 : ℝ)+2*(67324399687/100837500000000 : ℝ)*(17533/100000 : ℝ)=(10001139236513771/10000000000000000 : ℝ) by norm_num, show 1+2*(5379740524313573/20000000000000000000 : ℝ)=(10005379740524313573/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (80660303841761195921/80670000000000000000 : ℝ)*(X 1 0+X 2 0)+(67324399687/100837500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4835/1024 : ℝ)) (lo := (4733/50000 : ℝ)) (hi := (17533/100000 : ℝ)) (c := (80660303841761195921/80670000000000000000 : ℝ)) (alpha := (67324399687/100837500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (80660303841761195921/80670000000000000000 : ℝ)*(X 0 1+X 2 1)+(67324399687/100837500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4835/1024 : ℝ)) (lo := (4733/50000 : ℝ)) (hi := (17533/100000 : ℝ)) (c := (80660303841761195921/80670000000000000000 : ℝ)) (alpha := (67324399687/100837500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (80660303841761195921/80670000000000000000 : ℝ)*(X 0 2+X 1 2)+(67324399687/100837500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4835/1024 : ℝ)) (lo := (4733/50000 : ℝ)) (hi := (17533/100000 : ℝ)) (c := (80660303841761195921/80670000000000000000 : ℝ)) (alpha := (67324399687/100837500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-330837579/2000000000 : ℝ)*X 0 0+(2729268787/5000000000 : ℝ)*X 0 1+(5178083553/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352067109/10000000000 : ℝ)*X 1 0+(-1798829213/10000000000 : ℝ)*X 1 1+(2589041797/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338016789/2500000000 : ℝ)*X 2 0+(5178083483/10000000000 : ℝ)*X 2 1+(-899414649/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((419567177/1000000000 : ℝ)*X 0 0+(3853127979/10000000000 : ℝ)*X 0 1+(2280241449/5000000000 : ℝ)*X 0 2+(419567177/1000000000 : ℝ)*X 1 0+(3853127979/10000000000 : ℝ)*X 1 1+(2280241449/5000000000 : ℝ)*X 1 2+(419567177/1000000000 : ℝ)*X 2 0+(3853127979/10000000000 : ℝ)*X 2 1+(2280241449/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-330852409/2000000000 : ℝ)*X 0 0+(518026071/1000000000 : ℝ)*X 0 1+(5456336963/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2638667219/5000000000 : ℝ)*X 1 0+(-1520575731/10000000000 : ℝ)*X 1 1+(545633707/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((527733539/1000000000 : ℝ)*X 2 0+(5456335941/10000000000 : ℝ)*X 2 1+(-190071999/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2097929711/5000000000 : ℝ)*X 0 0+(910998681/2000000000 : ℝ)*X 0 1+(964669381/2500000000 : ℝ)*X 0 2+(2097929711/5000000000 : ℝ)*X 1 0+(910998681/2000000000 : ℝ)*X 1 1+(964669381/2500000000 : ℝ)*X 1 2+(2097929711/5000000000 : ℝ)*X 2 0+(910998681/2000000000 : ℝ)*X 2 1+(964669381/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1266960994410405836156240637/268900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (351909299/50000000000000 : ℝ)*(base19) + (674565761/100000000000000 : ℝ)*(base23) + (3241493/10000000000000 : ℝ)*(lower2) + (1451467/1000000000000 : ℝ)*(upper3) + (4063683/10000000000000 : ℝ)*(upper5) + (497938795539603/20000000000000 : ℝ)*(major0) + (497938795539603/20000000000000 : ℝ)*(major1) + (77802936803063/3125000000000 : ℝ)*(major2) + (1782828031540337/50000000000000 : ℝ)*(sp0) + (3565662864937049/100000000000000 : ℝ)*(sp1) + (1782831447094943/50000000000000 : ℝ)*(sp2) + (1413720327457437/100000000000000 : ℝ)*(sp3) + (7505674973/100000000000000 : ℝ)*(sp4) + (3902128149/100000000000000 : ℝ)*(sp7) + (706862114792793/50000000000000 : ℝ)*(f.failure) + (55713493261807/1562500000000 : ℝ)*(f.sum) + (167756703439067/40335000000000000000000000000 : ℝ)*base66 + (996957543755320637/1613400000000000000000000000000000 : ℝ)*base68 + (12371799067125227/252093750000000000000000000000000 : ℝ)*base70 + (6537133475655679363/1613400000000000000000000000000000 : ℝ)*base71 + (130803273994303/40335000000000000000000000000 : ℝ)*base73 + (1178974764376781023/252093750000000000000000000000000 : ℝ)*base75 + (680604943060253121/537800000000000000000000000000000 : ℝ)*base77 + (1020530832728653121/537800000000000000000000000000000 : ℝ)*base79 + (531920472489/268900000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (6253161/1000000000000000000000 : ℝ)*base89 + (6253161/1000000000000000000000 : ℝ)*base91 + (3746839/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2778006126064916547092122023/336125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (935032961/100000000000000 : ℝ)*(base19) + (1914385771/100000000000000 : ℝ)*(base23) + (169487757/100000000000000 : ℝ)*(upper3) + (1143289/800000000000 : ℝ)*(lower4) + (632289767466979/25000000000000 : ℝ)*(major0) + (632289767466979/25000000000000 : ℝ)*(major1) + (632289767466979/25000000000000 : ℝ)*(major2) + (2642528293/25000000000000 : ℝ)*(sp1) + (11299541/78125000000 : ℝ)*(sp2) + (277231841/25000000000000 : ℝ)*(sp3) + (1811092075395657/50000000000000 : ℝ)*(sp4) + (1811086322822591/50000000000000 : ℝ)*(sp5) + (452770971624133/12500000000000 : ℝ)*(sp6) + (718066302261893/50000000000000 : ℝ)*(sp7) + (28722674269023/2000000000000 : ℝ)*(f.failure) + (1811092075395657/50000000000000 : ℝ)*(f.sum) + (69828941448133/20167500000000000000000000000 : ℝ)*base65 + (24181866801139892659/2016750000000000000000000000000000 : ℝ)*base67 + (25528603056898892659/2016750000000000000000000000000000 : ℝ)*base69 + (17900412930822392659/2016750000000000000000000000000000 : ℝ)*base71 + (8108143957541/2520937500000000000000000000 : ℝ)*base73 + (3359564341338392659/2016750000000000000000000000000000 : ℝ)*base75 + (28399604605524392659/2016750000000000000000000000000000 : ℝ)*base77 + (13235939792062892659/2016750000000000000000000000000000 : ℝ)*base79 + (10585541841791/2520937500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (286129/40000000000000000000 : ℝ)*base90 + (286129/40000000000000000000 : ℝ)*base92 + (286129/40000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1630_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35221777/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17533/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4733/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5231/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3283/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1630_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1630_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35221777/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5231/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3283/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1630_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1630_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1630_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35221777/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5231/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3283/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1630_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

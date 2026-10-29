-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1479_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:12:36.457+00:00
-- url     : https://prove2.me/submissions/c4731c75-632c-47f2-9050-212864e4683b

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
theorem support_rectangle_w1479_s6_0 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1917893007/10000000000 : ℝ)*x 0 + (1359390433/2500000000 : ℝ)*x 1 + (5215786407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1917893007/10000000000 : ℝ)^4455 ≤ (11716004709597/100000000000000 : ℝ)^3431 := by
    have hnat : (1917893007 : ℕ)^4455*100000000000000^3431 ≤ 11716004709597^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1917893007 10000000000 11716004709597 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359390433/2500000000 : ℝ)^4455 ≤ (2833441232209/6250000000000 : ℝ)^3431 := by
    have hnat : (1359390433 : ℕ)^4455*6250000000000^3431 ≤ 2833441232209^3431*2500000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359390433 2500000000 2833441232209 6250000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215786407/10000000000 : ℝ)^4455 ≤ (8589787112013/20000000000000 : ℝ)^3431 := by
    have hnat : (5215786407 : ℕ)^4455*20000000000000^3431 ≤ 8589787112013^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215786407 10000000000 8589787112013 20000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1917893007/10000000000 : ℝ), (1359390433/2500000000 : ℝ), (5215786407/10000000000 : ℝ)] ![(11716004709597/100000000000000 : ℝ), (2833441232209/6250000000000 : ℝ), (8589787112013/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1917893007/10000000000 : ℝ)|^4455 ≤ (11716004709597/100000000000000 : ℝ)^3431
        have hw : |(-1917893007/10000000000 : ℝ)|=(1917893007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359390433/2500000000 : ℝ)|^4455 ≤ (2833441232209/6250000000000 : ℝ)^3431
        have hw : |(1359390433/2500000000 : ℝ)|=(1359390433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215786407/10000000000 : ℝ)|^4455 ≤ (8589787112013/20000000000000 : ℝ)^3431
        have hw : |(5215786407/10000000000 : ℝ)|=(5215786407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s6_1 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676680197/5000000000 : ℝ)*x 0 + (-7935759/39062500 : ℝ)*x 1 + (65197331/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676680197/5000000000 : ℝ)^4455 ≤ (44425633278221/100000000000000 : ℝ)^3431 := by
    have hnat : (2676680197 : ℕ)^4455*100000000000000^3431 ≤ 44425633278221^3431*5000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676680197 5000000000 44425633278221 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7935759/39062500 : ℝ)^4455 ≤ (6312715181317/50000000000000 : ℝ)^3431 := by
    have hnat : (7935759 : ℕ)^4455*50000000000000^3431 ≤ 6312715181317^3431*39062500^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7935759 39062500 6312715181317 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65197331/125000000 : ℝ)^4455 ≤ (21474468170291/50000000000000 : ℝ)^3431 := by
    have hnat : (65197331 : ℕ)^4455*50000000000000^3431 ≤ 21474468170291^3431*125000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65197331 125000000 21474468170291 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676680197/5000000000 : ℝ), (-7935759/39062500 : ℝ), (65197331/125000000 : ℝ)] ![(44425633278221/100000000000000 : ℝ), (6312715181317/50000000000000 : ℝ), (21474468170291/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676680197/5000000000 : ℝ)|^4455 ≤ (44425633278221/100000000000000 : ℝ)^3431
        have hw : |(2676680197/5000000000 : ℝ)|=(2676680197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7935759/39062500 : ℝ)|^4455 ≤ (6312715181317/50000000000000 : ℝ)^3431
        have hw : |(-7935759/39062500 : ℝ)|=(7935759/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65197331/125000000 : ℝ)|^4455 ≤ (21474468170291/50000000000000 : ℝ)^3431
        have hw : |(65197331/125000000 : ℝ)|=(65197331/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s6_2 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338340103/2500000000 : ℝ)*x 0 + (41726291/80000000 : ℝ)*x 1 + (-101577721/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338340103/2500000000 : ℝ)^4455 ≤ (22212816736089/50000000000000 : ℝ)^3431 := by
    have hnat : (1338340103 : ℕ)^4455*50000000000000^3431 ≤ 22212816736089^3431*2500000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338340103 2500000000 22212816736089 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41726291/80000000 : ℝ)^4455 ≤ (33553855639/78125000000 : ℝ)^3431 := by
    have hnat : (41726291 : ℕ)^4455*78125000000^3431 ≤ 33553855639^3431*80000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41726291 80000000 33553855639 78125000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (101577721/500000000 : ℝ)^4455 ≤ (3156357824673/25000000000000 : ℝ)^3431 := by
    have hnat : (101577721 : ℕ)^4455*25000000000000^3431 ≤ 3156357824673^3431*500000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101577721 500000000 3156357824673 25000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338340103/2500000000 : ℝ), (41726291/80000000 : ℝ), (-101577721/500000000 : ℝ)] ![(22212816736089/50000000000000 : ℝ), (33553855639/78125000000 : ℝ), (3156357824673/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338340103/2500000000 : ℝ)|^4455 ≤ (22212816736089/50000000000000 : ℝ)^3431
        have hw : |(1338340103/2500000000 : ℝ)|=(1338340103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41726291/80000000 : ℝ)|^4455 ≤ (33553855639/78125000000 : ℝ)^3431
        have hw : |(41726291/80000000 : ℝ)|=(41726291/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-101577721/500000000 : ℝ)|^4455 ≤ (3156357824673/25000000000000 : ℝ)^3431
        have hw : |(-101577721/500000000 : ℝ)|=(101577721/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s6_3 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071347853/2500000000 : ℝ)*x 0 + (4045923579/10000000000 : ℝ)*x 1 + (1134286591/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071347853/2500000000 : ℝ)^4455 ≤ (1331116642911/4000000000000 : ℝ)^3431 := by
    have hnat : (1071347853 : ℕ)^4455*4000000000000^3431 ≤ 1331116642911^3431*2500000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071347853 2500000000 1331116642911 4000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4045923579/10000000000 : ℝ)^4455 ≤ (30883750351567/100000000000000 : ℝ)^3431 := by
    have hnat : (4045923579 : ℕ)^4455*100000000000000^3431 ≤ 30883750351567^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4045923579 10000000000 30883750351567 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1134286591/2500000000 : ℝ)^4455 ≤ (1119947923801/3125000000000 : ℝ)^3431 := by
    have hnat : (1134286591 : ℕ)^4455*3125000000000^3431 ≤ 1119947923801^3431*2500000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134286591 2500000000 1119947923801 3125000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071347853/2500000000 : ℝ), (4045923579/10000000000 : ℝ), (1134286591/2500000000 : ℝ)] ![(1331116642911/4000000000000 : ℝ), (30883750351567/100000000000000 : ℝ), (1119947923801/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071347853/2500000000 : ℝ)|^4455 ≤ (1331116642911/4000000000000 : ℝ)^3431
        have hw : |(1071347853/2500000000 : ℝ)|=(1071347853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4045923579/10000000000 : ℝ)|^4455 ≤ (30883750351567/100000000000000 : ℝ)^3431
        have hw : |(4045923579/10000000000 : ℝ)|=(4045923579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1134286591/2500000000 : ℝ)|^4455 ≤ (1119947923801/3125000000000 : ℝ)^3431
        have hw : |(1134286591/2500000000 : ℝ)|=(1134286591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s6_4 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-479480847/2500000000 : ℝ)*x 0 + (5216920733/10000000000 : ℝ)*x 1 + (1359104771/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (479480847/2500000000 : ℝ)^4455 ≤ (732265355747/6250000000000 : ℝ)^3431 := by
    have hnat : (479480847 : ℕ)^4455*6250000000000^3431 ≤ 732265355747^3431*2500000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      479480847 2500000000 732265355747 6250000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216920733/10000000000 : ℝ)^4455 ≤ (4296106418531/10000000000000 : ℝ)^3431 := by
    have hnat : (5216920733 : ℕ)^4455*10000000000000^3431 ≤ 4296106418531^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216920733 10000000000 4296106418531 10000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1359104771/2500000000 : ℝ)^4455 ≤ (45322690110501/100000000000000 : ℝ)^3431 := by
    have hnat : (1359104771 : ℕ)^4455*100000000000000^3431 ≤ 45322690110501^3431*2500000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359104771 2500000000 45322690110501 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-479480847/2500000000 : ℝ), (5216920733/10000000000 : ℝ), (1359104771/2500000000 : ℝ)] ![(732265355747/6250000000000 : ℝ), (4296106418531/10000000000000 : ℝ), (45322690110501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-479480847/2500000000 : ℝ)|^4455 ≤ (732265355747/6250000000000 : ℝ)^3431
        have hw : |(-479480847/2500000000 : ℝ)|=(479480847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216920733/10000000000 : ℝ)|^4455 ≤ (4296106418531/10000000000000 : ℝ)^3431
        have hw : |(5216920733/10000000000 : ℝ)|=(5216920733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1359104771/2500000000 : ℝ)|^4455 ≤ (45322690110501/100000000000000 : ℝ)^3431
        have hw : |(1359104771/2500000000 : ℝ)|=(1359104771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s6_5 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323862729/2500000000 : ℝ)*x 0 + (-1810921663/10000000000 : ℝ)*x 1 + (217456763/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323862729/2500000000 : ℝ)^4455 ≤ (43802644286341/100000000000000 : ℝ)^3431 := by
    have hnat : (1323862729 : ℕ)^4455*100000000000000^3431 ≤ 43802644286341^3431*2500000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323862729 2500000000 43802644286341 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1810921663/10000000000 : ℝ)^4455 ≤ (5437332843659/50000000000000 : ℝ)^3431 := by
    have hnat : (1810921663 : ℕ)^4455*50000000000000^3431 ≤ 5437332843659^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1810921663 10000000000 5437332843659 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217456763/400000000 : ℝ)^4455 ≤ (1812907600523/4000000000000 : ℝ)^3431 := by
    have hnat : (217456763 : ℕ)^4455*4000000000000^3431 ≤ 1812907600523^3431*400000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217456763 400000000 1812907600523 4000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323862729/2500000000 : ℝ), (-1810921663/10000000000 : ℝ), (217456763/400000000 : ℝ)] ![(43802644286341/100000000000000 : ℝ), (5437332843659/50000000000000 : ℝ), (1812907600523/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323862729/2500000000 : ℝ)|^4455 ≤ (43802644286341/100000000000000 : ℝ)^3431
        have hw : |(1323862729/2500000000 : ℝ)|=(1323862729/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1810921663/10000000000 : ℝ)|^4455 ≤ (5437332843659/50000000000000 : ℝ)^3431
        have hw : |(-1810921663/10000000000 : ℝ)|=(1810921663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(217456763/400000000 : ℝ)|^4455 ≤ (1812907600523/4000000000000 : ℝ)^3431
        have hw : |(217456763/400000000 : ℝ)|=(217456763/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s6_6 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647725461/5000000000 : ℝ)*x 0 + (135910477/250000000 : ℝ)*x 1 + (-113182603/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647725461/5000000000 : ℝ)^4455 ≤ (684416317981/1562500000000 : ℝ)^3431 := by
    have hnat : (2647725461 : ℕ)^4455*1562500000000^3431 ≤ 684416317981^3431*5000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647725461 5000000000 684416317981 1562500000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135910477/250000000 : ℝ)^4455 ≤ (7081670323/15625000000 : ℝ)^3431 := by
    have hnat : (135910477 : ℕ)^4455*15625000000^3431 ≤ 7081670323^3431*250000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135910477 250000000 7081670323 15625000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (113182603/625000000 : ℝ)^4455 ≤ (10874665570359/100000000000000 : ℝ)^3431 := by
    have hnat : (113182603 : ℕ)^4455*100000000000000^3431 ≤ 10874665570359^3431*625000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113182603 625000000 10874665570359 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647725461/5000000000 : ℝ), (135910477/250000000 : ℝ), (-113182603/625000000 : ℝ)] ![(684416317981/1562500000000 : ℝ), (7081670323/15625000000 : ℝ), (10874665570359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647725461/5000000000 : ℝ)|^4455 ≤ (684416317981/1562500000000 : ℝ)^3431
        have hw : |(2647725461/5000000000 : ℝ)|=(2647725461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(135910477/250000000 : ℝ)|^4455 ≤ (7081670323/15625000000 : ℝ)^3431
        have hw : |(135910477/250000000 : ℝ)|=(135910477/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-113182603/625000000 : ℝ)|^4455 ≤ (10874665570359/100000000000000 : ℝ)^3431
        have hw : |(-113182603/625000000 : ℝ)|=(113182603/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s6_7 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4285458767/10000000000 : ℝ)*x 0 + (4534633933/10000000000 : ℝ)*x 1 + (253028403/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4285458767/10000000000 : ℝ)^4455 ≤ (33278595219291/100000000000000 : ℝ)^3431 := by
    have hnat : (4285458767 : ℕ)^4455*100000000000000^3431 ≤ 33278595219291^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4285458767 10000000000 33278595219291 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4534633933/10000000000 : ℝ)^4455 ≤ (35812567368497/100000000000000 : ℝ)^3431 := by
    have hnat : (4534633933 : ℕ)^4455*100000000000000^3431 ≤ 35812567368497^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4534633933 10000000000 35812567368497 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (253028403/625000000 : ℝ)^4455 ≤ (30908837398757/100000000000000 : ℝ)^3431 := by
    have hnat : (253028403 : ℕ)^4455*100000000000000^3431 ≤ 30908837398757^3431*625000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253028403 625000000 30908837398757 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4285458767/10000000000 : ℝ), (4534633933/10000000000 : ℝ), (253028403/625000000 : ℝ)] ![(33278595219291/100000000000000 : ℝ), (35812567368497/100000000000000 : ℝ), (30908837398757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4285458767/10000000000 : ℝ)|^4455 ≤ (33278595219291/100000000000000 : ℝ)^3431
        have hw : |(4285458767/10000000000 : ℝ)|=(4285458767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4534633933/10000000000 : ℝ)|^4455 ≤ (35812567368497/100000000000000 : ℝ)^3431
        have hw : |(4534633933/10000000000 : ℝ)|=(4534633933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(253028403/625000000 : ℝ)|^4455 ≤ (30908837398757/100000000000000 : ℝ)^3431
        have hw : |(253028403/625000000 : ℝ)|=(253028403/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1479_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32149573/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15477/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (539/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (5391/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (619/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15477/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (539/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15477/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (539/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15477/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (539/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15477/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (539/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15477/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (539/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15477/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (539/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (539/5000 : ℝ) ^ (4453/1024 : ℝ) ≤ (6211753326604963/100000000000000000000 : ℝ) := by
    have hpowers : (539/5000 : ℝ)^4453 ≤ (6211753326604963/100000000000000000000 : ℝ)^1024 := by
      have hnat : (539 : ℕ)^4453*100000000000000000000^1024 ≤ 6211753326604963^1024*5000^4453 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        539 5000 6211753326604963 100000000000000000000 4453 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (539/5000 : ℝ)) (X := (6211753326604963/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15477/100000 : ℝ) ^ (4453/1024 : ℝ) ≤ (29939555921498403/100000000000000000000 : ℝ) := by
    have hpowers : (15477/100000 : ℝ)^4453 ≤ (29939555921498403/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15477 : ℕ)^4453*100000000000000000000^1024 ≤ 29939555921498403^1024*100000^4453 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15477 100000 29939555921498403 100000000000000000000 4453 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15477/100000 : ℝ)) (X := (29939555921498403/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006211753326604963/50000000000000000000 : ℝ) ≤ (2500071418495059/2500000000000000 : ℝ) ^ (4453/1024 : ℝ) := by
    have hpowers : (50006211753326604963/50000000000000000000 : ℝ)^1024 ≤ (2500071418495059/2500000000000000 : ℝ)^4453 := by
      have hnat : (50006211753326604963 : ℕ)^1024*2500000000000000^4453 ≤ 2500071418495059^4453*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006211753326604963 50000000000000000000 2500071418495059 2500000000000000 1024 4453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500071418495059/2500000000000000 : ℝ)) (X := (50006211753326604963/50000000000000000000 : ℝ)) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018075654624051683/50000000000000000000 : ℝ) ≤ (10000831210175009/10000000000000000 : ℝ) ^ (4453/1024 : ℝ) := by
    have hpowers : (50018075654624051683/50000000000000000000 : ℝ)^1024 ≤ (10000831210175009/10000000000000000 : ℝ)^4453 := by
      have hnat : (50018075654624051683 : ℕ)^1024*10000000000000000^4453 ≤ 10000831210175009^4453*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018075654624051683 50000000000000000000 10000831210175009 10000000000000000 1024 4453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000831210175009/10000000000000000 : ℝ)) (X := (50018075654624051683/50000000000000000000 : ℝ)) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029939555921498403/50000000000000000000 : ℝ) ≤ (5000688373184891/5000000000000000 : ℝ) ^ (4453/1024 : ℝ) := by
    have hpowers : (50029939555921498403/50000000000000000000 : ℝ)^1024 ≤ (5000688373184891/5000000000000000 : ℝ)^4453 := by
      have hnat : (50029939555921498403 : ℕ)^1024*5000000000000000^4453 ≤ 5000688373184891^4453*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029939555921498403 50000000000000000000 5000688373184891 5000000000000000 1024 4453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000688373184891/5000000000000000 : ℝ)) (X := (50029939555921498403/50000000000000000000 : ℝ)) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6211753326604963/100000000000000000000 : ℝ) ≤ ((152466168994564489/152500000000000000 : ℝ)+2*(545536194773/469700000000000 : ℝ)*(539/5000 : ℝ))^(4453/1024 : ℝ) := by
    rw [show (152466168994564489/152500000000000000 : ℝ)+2*(545536194773/469700000000000 : ℝ)*(539/5000 : ℝ)=(2500071418495059/2500000000000000 : ℝ) by norm_num, show 1+2*(6211753326604963/100000000000000000000 : ℝ)=(50006211753326604963/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29939555921498403/100000000000000000000 : ℝ)+(6211753326604963/100000000000000000000 : ℝ) ≤ ((152466168994564489/152500000000000000 : ℝ)+(545536194773/469700000000000 : ℝ)*((15477/100000 : ℝ)+(539/5000 : ℝ)))^(4453/1024 : ℝ) := by
    rw [show (152466168994564489/152500000000000000 : ℝ)+(545536194773/469700000000000 : ℝ)*((15477/100000 : ℝ)+(539/5000 : ℝ))=(10000831210175009/10000000000000000 : ℝ) by norm_num, show 1+(29939555921498403/100000000000000000000 : ℝ)+(6211753326604963/100000000000000000000 : ℝ)=(50018075654624051683/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29939555921498403/100000000000000000000 : ℝ) ≤ ((152466168994564489/152500000000000000 : ℝ)+2*(545536194773/469700000000000 : ℝ)*(15477/100000 : ℝ))^(4453/1024 : ℝ) := by
    rw [show (152466168994564489/152500000000000000 : ℝ)+2*(545536194773/469700000000000 : ℝ)*(15477/100000 : ℝ)=(5000688373184891/5000000000000000 : ℝ) by norm_num, show 1+2*(29939555921498403/100000000000000000000 : ℝ)=(50029939555921498403/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (152466168994564489/152500000000000000 : ℝ)*(X 1 0+X 2 0)+(545536194773/469700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4453/1024 : ℝ)) (lo := (539/5000 : ℝ)) (hi := (15477/100000 : ℝ)) (c := (152466168994564489/152500000000000000 : ℝ)) (alpha := (545536194773/469700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (152466168994564489/152500000000000000 : ℝ)*(X 0 1+X 2 1)+(545536194773/469700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4453/1024 : ℝ)) (lo := (539/5000 : ℝ)) (hi := (15477/100000 : ℝ)) (c := (152466168994564489/152500000000000000 : ℝ)) (alpha := (545536194773/469700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (152466168994564489/152500000000000000 : ℝ)*(X 0 2+X 1 2)+(545536194773/469700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4453/1024 : ℝ)) (lo := (539/5000 : ℝ)) (hi := (15477/100000 : ℝ)) (c := (152466168994564489/152500000000000000 : ℝ)) (alpha := (545536194773/469700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1917893007/10000000000 : ℝ)*X 0 0+(1359390433/2500000000 : ℝ)*X 0 1+(5215786407/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676680197/5000000000 : ℝ)*X 1 0+(-7935759/39062500 : ℝ)*X 1 1+(65197331/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338340103/2500000000 : ℝ)*X 2 0+(41726291/80000000 : ℝ)*X 2 1+(-101577721/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1071347853/2500000000 : ℝ)*X 0 0+(4045923579/10000000000 : ℝ)*X 0 1+(1134286591/2500000000 : ℝ)*X 0 2+(1071347853/2500000000 : ℝ)*X 1 0+(4045923579/10000000000 : ℝ)*X 1 1+(1134286591/2500000000 : ℝ)*X 1 2+(1071347853/2500000000 : ℝ)*X 2 0+(4045923579/10000000000 : ℝ)*X 2 1+(1134286591/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-479480847/2500000000 : ℝ)*X 0 0+(5216920733/10000000000 : ℝ)*X 0 1+(1359104771/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323862729/2500000000 : ℝ)*X 1 0+(-1810921663/10000000000 : ℝ)*X 1 1+(217456763/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647725461/5000000000 : ℝ)*X 2 0+(135910477/250000000 : ℝ)*X 2 1+(-113182603/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4285458767/10000000000 : ℝ)*X 0 0+(4534633933/10000000000 : ℝ)*X 0 1+(253028403/625000000 : ℝ)*X 0 2+(4285458767/10000000000 : ℝ)*X 1 0+(4534633933/10000000000 : ℝ)*X 1 1+(253028403/625000000 : ℝ)*X 1 2+(4285458767/10000000000 : ℝ)*X 2 0+(4534633933/10000000000 : ℝ)*X 2 1+(253028403/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (619252238162998693742552097/146781250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (328185237/50000000000000 : ℝ)*(base19) + (636441663/100000000000000 : ℝ)*(base23) + (18784969/100000000000000 : ℝ)*(lower2) + (155152911/100000000000000 : ℝ)*(upper3) + (23580633/100000000000000 : ℝ)*(upper5) + (818104239598111/25000000000000 : ℝ)*(major0) + (818104239598111/25000000000000 : ℝ)*(major1) + (818104239598111/25000000000000 : ℝ)*(major2) + (1127269968960233/25000000000000 : ℝ)*(sp0) + (1127271977994083/25000000000000 : ℝ)*(sp1) + (4509087931905143/100000000000000 : ℝ)*(sp2) + (2035739905271107/100000000000000 : ℝ)*(sp3) + (69540047/800000000000 : ℝ)*(sp4) + (1325634421/25000000000000 : ℝ)*(sp7) + (203574520780879/10000000000000 : ℝ)*(f.failure) + (4509088568346807/100000000000000 : ℝ)*(f.sum) + (1306399488133/5871250000000000000000000000 : ℝ)*base65 + (4020885452811493517/293562500000000000000000000000000 : ℝ)*base68 + (1178222737033993517/293562500000000000000000000000000 : ℝ)*base70 + (2033913482924743517/293562500000000000000000000000000 : ℝ)*base72 + (221580519681333/23485000000000000000000000000 : ℝ)*base74 + (2667659501695993517/293562500000000000000000000000000 : ℝ)*base76 + (2116464463879493517/293562500000000000000000000000000 : ℝ)*base78 + (638342671819118517/293562500000000000000000000000000 : ℝ)*base80 + (20351562398753/5871250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1585333/200000000000000000000 : ℝ)*base90 + (1585333/200000000000000000000 : ℝ)*base92 + (1585333/200000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16297572442237243349266749/3669531250000000000000000000000 : ℝ) := by norm_num
    linear_combination (727953283/100000000000000 : ℝ)*(base19) + (404993959/50000000000000 : ℝ)*(base23) + (234802421/100000000000000 : ℝ)*(lower1) + (93304703/100000000000000 : ℝ)*(upper3) + (32944323/100000000000000 : ℝ)*(lower4) + (45882257/50000000000000 : ℝ)*(upper5) + (165317009783131/5000000000000 : ℝ)*(major0) + (165317009783131/5000000000000 : ℝ)*(major1) + (165317009783131/5000000000000 : ℝ)*(major2) + (670288949/50000000000000 : ℝ)*(sp2) + (4555831652687031/100000000000000 : ℝ)*(sp4) + (1138957731183437/25000000000000 : ℝ)*(sp5) + (911165900424243/20000000000000 : ℝ)*(sp6) + (514212147648527/25000000000000 : ℝ)*(sp7) + (514212147648527/25000000000000 : ℝ)*(f.failure) + (4555831652687031/100000000000000 : ℝ)*(f.sum) + (620399272719/1174250000000000000000000000 : ℝ)*base65 + (1068958956418887043/58712500000000000000000000000000 : ℝ)*base67 + (513455833666424543/58712500000000000000000000000000 : ℝ)*base69 + (981466908952024543/58712500000000000000000000000000 : ℝ)*base71 + (6352673024857/1174250000000000000000000000 : ℝ)*base74 + (999845243657524543/58712500000000000000000000000000 : ℝ)*base75 + (137171116883449543/58712500000000000000000000000000 : ℝ)*base77 + (195074681608850457/58712500000000000000000000000000 : ℝ)*base80 + (10214942222259/1174250000000000000000000000 : ℝ)*base82 + (2871029/500000000000000000000 : ℝ)*base90 + (2871029/500000000000000000000 : ℝ)*base92 + (2871029/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1479_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32149573/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15477/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (539/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5391/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (619/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1479_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1479_box_0 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-169816999/1000000000 : ℝ)*x 0 + (54064089/100000000 : ℝ)*x 1 + (5406409581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (169816999/1000000000 : ℝ)^4455 ≤ (10003799723447/100000000000000 : ℝ)^3431 := by
    have hnat : (169816999 : ℕ)^4455*100000000000000^3431 ≤ 10003799723447^3431*1000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169816999 1000000000 10003799723447 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54064089/100000000 : ℝ)^4455 ≤ (11249524113009/25000000000000 : ℝ)^3431 := by
    have hnat : (54064089 : ℕ)^4455*25000000000000^3431 ≤ 11249524113009^3431*100000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54064089 100000000 11249524113009 25000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406409581/10000000000 : ℝ)^4455 ≤ (11249525952931/25000000000000 : ℝ)^3431 := by
    have hnat : (5406409581 : ℕ)^4455*25000000000000^3431 ≤ 11249525952931^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406409581 10000000000 11249525952931 25000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-169816999/1000000000 : ℝ), (54064089/100000000 : ℝ), (5406409581/10000000000 : ℝ)] ![(10003799723447/100000000000000 : ℝ), (11249524113009/25000000000000 : ℝ), (11249525952931/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-169816999/1000000000 : ℝ)|^4455 ≤ (10003799723447/100000000000000 : ℝ)^3431
        have hw : |(-169816999/1000000000 : ℝ)|=(169816999/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54064089/100000000 : ℝ)|^4455 ≤ (11249524113009/25000000000000 : ℝ)^3431
        have hw : |(54064089/100000000 : ℝ)|=(54064089/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406409581/10000000000 : ℝ)|^4455 ≤ (11249525952931/25000000000000 : ℝ)^3431
        have hw : |(5406409581/10000000000 : ℝ)|=(5406409581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_box_1 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270211949/10000000000 : ℝ)*x 0 + (-471705277/2500000000 : ℝ)*x 1 + (5406409309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270211949/10000000000 : ℝ)^4455 ≤ (43531758258977/100000000000000 : ℝ)^3431 := by
    have hnat : (5270211949 : ℕ)^4455*100000000000000^3431 ≤ 43531758258977^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270211949 10000000000 43531758258977 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (471705277/2500000000 : ℝ)^4455 ≤ (5735070425821/50000000000000 : ℝ)^3431 := by
    have hnat : (471705277 : ℕ)^4455*50000000000000^3431 ≤ 5735070425821^3431*2500000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471705277 2500000000 5735070425821 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406409309/10000000000 : ℝ)^4455 ≤ (11249525218043/25000000000000 : ℝ)^3431 := by
    have hnat : (5406409309 : ℕ)^4455*25000000000000^3431 ≤ 11249525218043^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406409309 10000000000 11249525218043 25000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270211949/10000000000 : ℝ), (-471705277/2500000000 : ℝ), (5406409309/10000000000 : ℝ)] ![(43531758258977/100000000000000 : ℝ), (5735070425821/50000000000000 : ℝ), (11249525218043/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270211949/10000000000 : ℝ)|^4455 ≤ (43531758258977/100000000000000 : ℝ)^3431
        have hw : |(5270211949/10000000000 : ℝ)|=(5270211949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-471705277/2500000000 : ℝ)|^4455 ≤ (5735070425821/50000000000000 : ℝ)^3431
        have hw : |(-471705277/2500000000 : ℝ)|=(471705277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406409309/10000000000 : ℝ)|^4455 ≤ (11249525218043/25000000000000 : ℝ)^3431
        have hw : |(5406409309/10000000000 : ℝ)|=(5406409309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_box_2 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2635105967/5000000000 : ℝ)*x 0 + (5406408469/10000000000 : ℝ)*x 1 + (-943411139/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2635105967/5000000000 : ℝ)^4455 ≤ (43531758098099/100000000000000 : ℝ)^3431 := by
    have hnat : (2635105967 : ℕ)^4455*100000000000000^3431 ≤ 43531758098099^3431*5000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635105967 5000000000 43531758098099 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406408469/10000000000 : ℝ)^4455 ≤ (44998091794143/100000000000000 : ℝ)^3431 := by
    have hnat : (5406408469 : ℕ)^4455*100000000000000^3431 ≤ 44998091794143^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406408469 10000000000 44998091794143 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (943411139/5000000000 : ℝ)^4455 ≤ (573507504347/5000000000000 : ℝ)^3431 := by
    have hnat : (943411139 : ℕ)^4455*5000000000000^3431 ≤ 573507504347^3431*5000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943411139 5000000000 573507504347 5000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2635105967/5000000000 : ℝ), (5406408469/10000000000 : ℝ), (-943411139/5000000000 : ℝ)] ![(43531758098099/100000000000000 : ℝ), (44998091794143/100000000000000 : ℝ), (573507504347/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2635105967/5000000000 : ℝ)|^4455 ≤ (43531758098099/100000000000000 : ℝ)^3431
        have hw : |(2635105967/5000000000 : ℝ)|=(2635105967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406408469/10000000000 : ℝ)|^4455 ≤ (44998091794143/100000000000000 : ℝ)^3431
        have hw : |(5406408469/10000000000 : ℝ)|=(5406408469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-943411139/5000000000 : ℝ)|^4455 ≤ (573507504347/5000000000000 : ℝ)^3431
        have hw : |(-943411139/5000000000 : ℝ)|=(943411139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_box_3 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2245021781/5000000000 : ℝ)*x 0 + (2095135879/5000000000 : ℝ)*x 1 + (1047567803/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2245021781/5000000000 : ℝ)^4455 ≤ (2209748869499/6250000000000 : ℝ)^3431 := by
    have hnat : (2245021781 : ℕ)^4455*6250000000000^3431 ≤ 2209748869499^3431*5000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245021781 5000000000 2209748869499 6250000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2095135879/5000000000 : ℝ)^4455 ≤ (16161005884333/50000000000000 : ℝ)^3431 := by
    have hnat : (2095135879 : ℕ)^4455*50000000000000^3431 ≤ 16161005884333^3431*5000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095135879 5000000000 16161005884333 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1047567803/2500000000 : ℝ)^4455 ≤ (3232200630007/10000000000000 : ℝ)^3431 := by
    have hnat : (1047567803 : ℕ)^4455*10000000000000^3431 ≤ 3232200630007^3431*2500000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047567803 2500000000 3232200630007 10000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2245021781/5000000000 : ℝ), (2095135879/5000000000 : ℝ), (1047567803/2500000000 : ℝ)] ![(2209748869499/6250000000000 : ℝ), (16161005884333/50000000000000 : ℝ), (3232200630007/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2245021781/5000000000 : ℝ)|^4455 ≤ (2209748869499/6250000000000 : ℝ)^3431
        have hw : |(2245021781/5000000000 : ℝ)|=(2245021781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2095135879/5000000000 : ℝ)|^4455 ≤ (16161005884333/50000000000000 : ℝ)^3431
        have hw : |(2095135879/5000000000 : ℝ)|=(2095135879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1047567803/2500000000 : ℝ)|^4455 ≤ (3232200630007/10000000000000 : ℝ)^3431
        have hw : |(1047567803/2500000000 : ℝ)|=(1047567803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_box_4 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-535771011/2500000000 : ℝ)*x 0 + (81912419/156250000 : ℝ)*x 1 + (2621197637/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535771011/2500000000 : ℝ)^4455 ≤ (169158703009/1250000000000 : ℝ)^3431 := by
    have hnat : (535771011 : ℕ)^4455*1250000000000^3431 ≤ 169158703009^3431*2500000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535771011 2500000000 169158703009 1250000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81912419/156250000 : ℝ)^4455 ≤ (21616824709629/50000000000000 : ℝ)^3431 := by
    have hnat : (81912419 : ℕ)^4455*50000000000000^3431 ≤ 21616824709629^3431*156250000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81912419 156250000 21616824709629 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621197637/5000000000 : ℝ)^4455 ≤ (10808413580911/25000000000000 : ℝ)^3431 := by
    have hnat : (2621197637 : ℕ)^4455*25000000000000^3431 ≤ 10808413580911^3431*5000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621197637 5000000000 10808413580911 25000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-535771011/2500000000 : ℝ), (81912419/156250000 : ℝ), (2621197637/5000000000 : ℝ)] ![(169158703009/1250000000000 : ℝ), (21616824709629/50000000000000 : ℝ), (10808413580911/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-535771011/2500000000 : ℝ)|^4455 ≤ (169158703009/1250000000000 : ℝ)^3431
        have hw : |(-535771011/2500000000 : ℝ)|=(535771011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(81912419/156250000 : ℝ)|^4455 ≤ (21616824709629/50000000000000 : ℝ)^3431
        have hw : |(81912419/156250000 : ℝ)|=(81912419/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621197637/5000000000 : ℝ)|^4455 ≤ (10808413580911/25000000000000 : ℝ)^3431
        have hw : |(2621197637/5000000000 : ℝ)|=(2621197637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_box_5 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2692348493/5000000000 : ℝ)*x 0 + (-244242887/1250000000 : ℝ)*x 1 + (262119767/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2692348493/5000000000 : ℝ)^4455 ≤ (44763592718719/100000000000000 : ℝ)^3431 := by
    have hnat : (2692348493 : ℕ)^4455*100000000000000^3431 ≤ 44763592718719^3431*5000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692348493 5000000000 44763592718719 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (244242887/1250000000 : ℝ)^4455 ≤ (12002752237269/100000000000000 : ℝ)^3431 := by
    have hnat : (244242887 : ℕ)^4455*100000000000000^3431 ≤ 12002752237269^3431*1250000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244242887 1250000000 12002752237269 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262119767/500000000 : ℝ)^4455 ≤ (4323365503039/10000000000000 : ℝ)^3431 := by
    have hnat : (262119767 : ℕ)^4455*10000000000000^3431 ≤ 4323365503039^3431*500000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262119767 500000000 4323365503039 10000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2692348493/5000000000 : ℝ), (-244242887/1250000000 : ℝ), (262119767/500000000 : ℝ)] ![(44763592718719/100000000000000 : ℝ), (12002752237269/100000000000000 : ℝ), (4323365503039/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2692348493/5000000000 : ℝ)|^4455 ≤ (44763592718719/100000000000000 : ℝ)^3431
        have hw : |(2692348493/5000000000 : ℝ)|=(2692348493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-244242887/1250000000 : ℝ)|^4455 ≤ (12002752237269/100000000000000 : ℝ)^3431
        have hw : |(-244242887/1250000000 : ℝ)|=(244242887/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262119767/500000000 : ℝ)|^4455 ≤ (4323365503039/10000000000000 : ℝ)^3431
        have hw : |(262119767/500000000 : ℝ)|=(262119767/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_box_6 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (134617429/250000000 : ℝ)*x 0 + (52423951/100000000 : ℝ)*x 1 + (-1953943183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134617429/250000000 : ℝ)^4455 ≤ (44763594596911/100000000000000 : ℝ)^3431 := by
    have hnat : (134617429 : ℕ)^4455*100000000000000^3431 ≤ 44763594596911^3431*250000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134617429 250000000 44763594596911 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52423951/100000000 : ℝ)^4455 ≤ (21616826230203/50000000000000 : ℝ)^3431 := by
    have hnat : (52423951 : ℕ)^4455*50000000000000^3431 ≤ 21616826230203^3431*100000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52423951 100000000 21616826230203 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1953943183/10000000000 : ℝ)^4455 ≤ (6001376465599/50000000000000 : ℝ)^3431 := by
    have hnat : (1953943183 : ℕ)^4455*50000000000000^3431 ≤ 6001376465599^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1953943183 10000000000 6001376465599 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134617429/250000000 : ℝ), (52423951/100000000 : ℝ), (-1953943183/10000000000 : ℝ)] ![(44763594596911/100000000000000 : ℝ), (21616826230203/50000000000000 : ℝ), (6001376465599/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134617429/250000000 : ℝ)|^4455 ≤ (44763594596911/100000000000000 : ℝ)^3431
        have hw : |(134617429/250000000 : ℝ)|=(134617429/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52423951/100000000 : ℝ)|^4455 ≤ (21616826230203/50000000000000 : ℝ)^3431
        have hw : |(52423951/100000000 : ℝ)|=(52423951/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1953943183/10000000000 : ℝ)|^4455 ≤ (6001376465599/50000000000000 : ℝ)^3431
        have hw : |(-1953943183/10000000000 : ℝ)|=(1953943183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_box_7 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4078485813/10000000000 : ℝ)*x 0 + (1098977871/2500000000 : ℝ)*x 1 + (549488951/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4078485813/10000000000 : ℝ)^4455 ≤ (31206877793061/100000000000000 : ℝ)^3431 := by
    have hnat : (4078485813 : ℕ)^4455*100000000000000^3431 ≤ 31206877793061^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4078485813 10000000000 31206877793061 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1098977871/2500000000 : ℝ)^4455 ≤ (17198280233071/50000000000000 : ℝ)^3431 := by
    have hnat : (1098977871 : ℕ)^4455*50000000000000^3431 ≤ 17198280233071^3431*2500000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098977871 2500000000 17198280233071 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (549488951/1250000000 : ℝ)^4455 ≤ (1719828086299/5000000000000 : ℝ)^3431 := by
    have hnat : (549488951 : ℕ)^4455*5000000000000^3431 ≤ 1719828086299^3431*1250000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549488951 1250000000 1719828086299 5000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4078485813/10000000000 : ℝ), (1098977871/2500000000 : ℝ), (549488951/1250000000 : ℝ)] ![(31206877793061/100000000000000 : ℝ), (17198280233071/50000000000000 : ℝ), (1719828086299/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4078485813/10000000000 : ℝ)|^4455 ≤ (31206877793061/100000000000000 : ℝ)^3431
        have hw : |(4078485813/10000000000 : ℝ)|=(4078485813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1098977871/2500000000 : ℝ)|^4455 ≤ (17198280233071/50000000000000 : ℝ)^3431
        have hw : |(1098977871/2500000000 : ℝ)|=(1098977871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(549488951/1250000000 : ℝ)|^4455 ≤ (1719828086299/5000000000000 : ℝ)^3431
        have hw : |(549488951/1250000000 : ℝ)|=(549488951/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_box_8 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2049253529/10000000000 : ℝ)*x 0 + (5127866949/10000000000 : ℝ)*x 1 + (5426956861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2049253529/10000000000 : ℝ)^4455 ≤ (2553687789457/20000000000000 : ℝ)^3431 := by
    have hnat : (2049253529 : ℕ)^4455*20000000000000^3431 ≤ 2553687789457^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049253529 10000000000 2553687789457 20000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5127866949/10000000000 : ℝ)^4455 ≤ (21005636655381/50000000000000 : ℝ)^3431 := by
    have hnat : (5127866949 : ℕ)^4455*50000000000000^3431 ≤ 21005636655381^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5127866949 10000000000 21005636655381 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426956861/10000000000 : ℝ)^4455 ≤ (4522028772861/10000000000000 : ℝ)^3431 := by
    have hnat : (5426956861 : ℕ)^4455*10000000000000^3431 ≤ 4522028772861^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426956861 10000000000 4522028772861 10000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2049253529/10000000000 : ℝ), (5127866949/10000000000 : ℝ), (5426956861/10000000000 : ℝ)] ![(2553687789457/20000000000000 : ℝ), (21005636655381/50000000000000 : ℝ), (4522028772861/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2049253529/10000000000 : ℝ)|^4455 ≤ (2553687789457/20000000000000 : ℝ)^3431
        have hw : |(-2049253529/10000000000 : ℝ)|=(2049253529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5127866949/10000000000 : ℝ)|^4455 ≤ (21005636655381/50000000000000 : ℝ)^3431
        have hw : |(5127866949/10000000000 : ℝ)|=(5127866949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426956861/10000000000 : ℝ)|^4455 ≤ (4522028772861/10000000000000 : ℝ)^3431
        have hw : |(5426956861/10000000000 : ℝ)|=(5426956861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_box_9 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (525586137/1000000000 : ℝ)*x 0 + (-1878158003/10000000000 : ℝ)*x 1 + (2713478333/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525586137/1000000000 : ℝ)^4455 ≤ (867558162197/2000000000000 : ℝ)^3431 := by
    have hnat : (525586137 : ℕ)^4455*2000000000000^3431 ≤ 867558162197^3431*1000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525586137 1000000000 867558162197 2000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1878158003/10000000000 : ℝ)^4455 ≤ (11401806258991/100000000000000 : ℝ)^3431 := by
    have hnat : (1878158003 : ℕ)^4455*100000000000000^3431 ≤ 11401806258991^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1878158003 10000000000 11401806258991 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2713478333/5000000000 : ℝ)^4455 ≤ (45220285618823/100000000000000 : ℝ)^3431 := by
    have hnat : (2713478333 : ℕ)^4455*100000000000000^3431 ≤ 45220285618823^3431*5000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713478333 5000000000 45220285618823 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525586137/1000000000 : ℝ), (-1878158003/10000000000 : ℝ), (2713478333/5000000000 : ℝ)] ![(867558162197/2000000000000 : ℝ), (11401806258991/100000000000000 : ℝ), (45220285618823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525586137/1000000000 : ℝ)|^4455 ≤ (867558162197/2000000000000 : ℝ)^3431
        have hw : |(525586137/1000000000 : ℝ)|=(525586137/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1878158003/10000000000 : ℝ)|^4455 ≤ (11401806258991/100000000000000 : ℝ)^3431
        have hw : |(-1878158003/10000000000 : ℝ)|=(1878158003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2713478333/5000000000 : ℝ)|^4455 ≤ (45220285618823/100000000000000 : ℝ)^3431
        have hw : |(2713478333/5000000000 : ℝ)|=(2713478333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_box_10 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5255861391/10000000000 : ℝ)*x 0 + (2713478583/5000000000 : ℝ)*x 1 + (-1878157287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5255861391/10000000000 : ℝ)^4455 ≤ (2711119270931/6250000000000 : ℝ)^3431 := by
    have hnat : (5255861391 : ℕ)^4455*6250000000000^3431 ≤ 2711119270931^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255861391 10000000000 2711119270931 6250000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713478583/5000000000 : ℝ)^4455 ≤ (45220291028533/100000000000000 : ℝ)^3431 := by
    have hnat : (2713478583 : ℕ)^4455*100000000000000^3431 ≤ 45220291028533^3431*5000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713478583 5000000000 45220291028533 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1878157287/10000000000 : ℝ)^4455 ≤ (5700900307531/50000000000000 : ℝ)^3431 := by
    have hnat : (1878157287 : ℕ)^4455*50000000000000^3431 ≤ 5700900307531^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1878157287 10000000000 5700900307531 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5255861391/10000000000 : ℝ), (2713478583/5000000000 : ℝ), (-1878157287/10000000000 : ℝ)] ![(2711119270931/6250000000000 : ℝ), (45220291028533/100000000000000 : ℝ), (5700900307531/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5255861391/10000000000 : ℝ)|^4455 ≤ (2711119270931/6250000000000 : ℝ)^3431
        have hw : |(5255861391/10000000000 : ℝ)|=(5255861391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713478583/5000000000 : ℝ)|^4455 ≤ (45220291028533/100000000000000 : ℝ)^3431
        have hw : |(2713478583/5000000000 : ℝ)|=(2713478583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1878157287/10000000000 : ℝ)|^4455 ≤ (5700900307531/50000000000000 : ℝ)^3431
        have hw : |(-1878157287/10000000000 : ℝ)|=(1878157287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_box_11 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4540449979/10000000000 : ℝ)*x 0 + (1041119183/2500000000 : ℝ)*x 1 + (1041119023/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4540449979/10000000000 : ℝ)^4455 ≤ (17936110104991/50000000000000 : ℝ)^3431 := by
    have hnat : (4540449979 : ℕ)^4455*50000000000000^3431 ≤ 17936110104991^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4540449979 10000000000 17936110104991 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1041119183/2500000000 : ℝ)^4455 ≤ (32063893087987/100000000000000 : ℝ)^3431 := by
    have hnat : (1041119183 : ℕ)^4455*100000000000000^3431 ≤ 32063893087987^3431*2500000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041119183 2500000000 32063893087987 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1041119023/2500000000 : ℝ)^4455 ≤ (16031943344857/50000000000000 : ℝ)^3431 := by
    have hnat : (1041119023 : ℕ)^4455*50000000000000^3431 ≤ 16031943344857^3431*2500000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041119023 2500000000 16031943344857 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4540449979/10000000000 : ℝ), (1041119183/2500000000 : ℝ), (1041119023/2500000000 : ℝ)] ![(17936110104991/50000000000000 : ℝ), (32063893087987/100000000000000 : ℝ), (16031943344857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4540449979/10000000000 : ℝ)|^4455 ≤ (17936110104991/50000000000000 : ℝ)^3431
        have hw : |(4540449979/10000000000 : ℝ)|=(4540449979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1041119183/2500000000 : ℝ)|^4455 ≤ (32063893087987/100000000000000 : ℝ)^3431
        have hw : |(1041119183/2500000000 : ℝ)|=(1041119183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1041119023/2500000000 : ℝ)|^4455 ≤ (16031943344857/50000000000000 : ℝ)^3431
        have hw : |(1041119023/2500000000 : ℝ)|=(1041119023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_box_12 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1792138347/10000000000 : ℝ)*x 0 + (344820967/625000000 : ℝ)*x 1 + (1306850897/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1792138347/10000000000 : ℝ)^4455 ≤ (2145686824123/20000000000000 : ℝ)^3431 := by
    have hnat : (1792138347 : ℕ)^4455*20000000000000^3431 ≤ 2145686824123^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1792138347 10000000000 2145686824123 20000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (344820967/625000000 : ℝ)^4455 ≤ (4619837795483/10000000000000 : ℝ)^3431 := by
    have hnat : (344820967 : ℕ)^4455*10000000000000^3431 ≤ 4619837795483^3431*625000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344820967 625000000 4619837795483 10000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1306850897/2500000000 : ℝ)^4455 ≤ (1722927516307/4000000000000 : ℝ)^3431 := by
    have hnat : (1306850897 : ℕ)^4455*4000000000000^3431 ≤ 1722927516307^3431*2500000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306850897 2500000000 1722927516307 4000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1792138347/10000000000 : ℝ), (344820967/625000000 : ℝ), (1306850897/2500000000 : ℝ)] ![(2145686824123/20000000000000 : ℝ), (4619837795483/10000000000000 : ℝ), (1722927516307/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1792138347/10000000000 : ℝ)|^4455 ≤ (2145686824123/20000000000000 : ℝ)^3431
        have hw : |(-1792138347/10000000000 : ℝ)|=(1792138347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(344820967/625000000 : ℝ)|^4455 ≤ (4619837795483/10000000000000 : ℝ)^3431
        have hw : |(344820967/625000000 : ℝ)|=(344820967/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1306850897/2500000000 : ℝ)|^4455 ≤ (1722927516307/4000000000000 : ℝ)^3431
        have hw : |(1306850897/2500000000 : ℝ)|=(1306850897/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_box_13 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5395160237/10000000000 : ℝ)*x 0 + (-1959894623/10000000000 : ℝ)*x 1 + (5227403569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5395160237/10000000000 : ℝ)^4455 ≤ (5609570991107/12500000000000 : ℝ)^3431 := by
    have hnat : (5395160237 : ℕ)^4455*12500000000000^3431 ≤ 5609570991107^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395160237 10000000000 5609570991107 12500000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1959894623/10000000000 : ℝ)^4455 ≤ (12050244355933/100000000000000 : ℝ)^3431 := by
    have hnat : (1959894623 : ℕ)^4455*100000000000000^3431 ≤ 12050244355933^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1959894623 10000000000 12050244355933 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5227403569/10000000000 : ℝ)^4455 ≤ (5384148463049/12500000000000 : ℝ)^3431 := by
    have hnat : (5227403569 : ℕ)^4455*12500000000000^3431 ≤ 5384148463049^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227403569 10000000000 5384148463049 12500000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5395160237/10000000000 : ℝ), (-1959894623/10000000000 : ℝ), (5227403569/10000000000 : ℝ)] ![(5609570991107/12500000000000 : ℝ), (12050244355933/100000000000000 : ℝ), (5384148463049/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5395160237/10000000000 : ℝ)|^4455 ≤ (5609570991107/12500000000000 : ℝ)^3431
        have hw : |(5395160237/10000000000 : ℝ)|=(5395160237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1959894623/10000000000 : ℝ)|^4455 ≤ (12050244355933/100000000000000 : ℝ)^3431
        have hw : |(-1959894623/10000000000 : ℝ)|=(1959894623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5227403569/10000000000 : ℝ)|^4455 ≤ (5384148463049/12500000000000 : ℝ)^3431
        have hw : |(5227403569/10000000000 : ℝ)|=(5227403569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_box_14 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (337197517/625000000 : ℝ)*x 0 + (2613701741/5000000000 : ℝ)*x 1 + (-489973673/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (337197517/625000000 : ℝ)^4455 ≤ (5609571038359/12500000000000 : ℝ)^3431 := by
    have hnat : (337197517 : ℕ)^4455*12500000000000^3431 ≤ 5609571038359^3431*625000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337197517 625000000 5609571038359 12500000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2613701741/5000000000 : ℝ)^4455 ≤ (673018543337/1562500000000 : ℝ)^3431 := by
    have hnat : (2613701741 : ℕ)^4455*1562500000000^3431 ≤ 673018543337^3431*5000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613701741 5000000000 673018543337 1562500000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (489973673/2500000000 : ℝ)^4455 ≤ (1205024490679/10000000000000 : ℝ)^3431 := by
    have hnat : (489973673 : ℕ)^4455*10000000000000^3431 ≤ 1205024490679^3431*2500000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489973673 2500000000 1205024490679 10000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(337197517/625000000 : ℝ), (2613701741/5000000000 : ℝ), (-489973673/2500000000 : ℝ)] ![(5609571038359/12500000000000 : ℝ), (673018543337/1562500000000 : ℝ), (1205024490679/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(337197517/625000000 : ℝ)|^4455 ≤ (5609571038359/12500000000000 : ℝ)^3431
        have hw : |(337197517/625000000 : ℝ)|=(337197517/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2613701741/5000000000 : ℝ)|^4455 ≤ (673018543337/1562500000000 : ℝ)^3431
        have hw : |(2613701741/5000000000 : ℝ)|=(2613701741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-489973673/2500000000 : ℝ)|^4455 ≤ (1205024490679/10000000000000 : ℝ)^3431
        have hw : |(-489973673/2500000000 : ℝ)|=(489973673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_box_15 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4040009351/10000000000 : ℝ)*x 0 + (2207342987/5000000000 : ℝ)*x 1 + (4414685463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4040009351/10000000000 : ℝ)^4455 ≤ (30825144277091/100000000000000 : ℝ)^3431 := by
    have hnat : (4040009351 : ℕ)^4455*100000000000000^3431 ≤ 30825144277091^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4040009351 10000000000 30825144277091 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2207342987/5000000000 : ℝ)^4455 ≤ (6917486090659/20000000000000 : ℝ)^3431 := by
    have hnat : (2207342987 : ℕ)^4455*20000000000000^3431 ≤ 6917486090659^3431*5000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207342987 5000000000 6917486090659 20000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4414685463/10000000000 : ℝ)^4455 ≤ (17293712627467/50000000000000 : ℝ)^3431 := by
    have hnat : (4414685463 : ℕ)^4455*50000000000000^3431 ≤ 17293712627467^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4414685463 10000000000 17293712627467 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4040009351/10000000000 : ℝ), (2207342987/5000000000 : ℝ), (4414685463/10000000000 : ℝ)] ![(30825144277091/100000000000000 : ℝ), (6917486090659/20000000000000 : ℝ), (17293712627467/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4040009351/10000000000 : ℝ)|^4455 ≤ (30825144277091/100000000000000 : ℝ)^3431
        have hw : |(4040009351/10000000000 : ℝ)|=(4040009351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2207342987/5000000000 : ℝ)|^4455 ≤ (6917486090659/20000000000000 : ℝ)^3431
        have hw : |(2207342987/5000000000 : ℝ)|=(2207342987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4414685463/10000000000 : ℝ)|^4455 ≤ (17293712627467/50000000000000 : ℝ)^3431
        have hw : |(4414685463/10000000000 : ℝ)|=(4414685463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1479_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32149573/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (619/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5391/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(63701/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58473/100000 : ℝ) ∧ (79957/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (85787/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (619/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5391/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (619/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5391/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (619/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5391/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (619/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5391/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (619/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5391/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (619/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5391/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5391/50000 : ℝ) ^ (4453/1024 : ℝ) ≤ (6216766504081113/100000000000000000000 : ℝ) := by
    have hpowers : (5391/50000 : ℝ)^4453 ≤ (6216766504081113/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5391 : ℕ)^4453*100000000000000000000^1024 ≤ 6216766504081113^1024*50000^4453 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5391 50000 6216766504081113 100000000000000000000 4453 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5391/50000 : ℝ)) (X := (6216766504081113/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (619/4000 : ℝ) ^ (4453/1024 : ℝ) ≤ (29922735094640351/100000000000000000000 : ℝ) := by
    have hpowers : (619/4000 : ℝ)^4453 ≤ (29922735094640351/100000000000000000000 : ℝ)^1024 := by
      have hnat : (619 : ℕ)^4453*100000000000000000000^1024 ≤ 29922735094640351^1024*4000^4453 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        619 4000 29922735094640351 100000000000000000000 4453 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (619/4000 : ℝ)) (X := (29922735094640351/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006216766504081113/50000000000000000000 : ℝ) ≤ (2500071476130389/2500000000000000 : ℝ) ^ (4453/1024 : ℝ) := by
    have hpowers : (50006216766504081113/50000000000000000000 : ℝ)^1024 ≤ (2500071476130389/2500000000000000 : ℝ)^4453 := by
      have hnat : (50006216766504081113 : ℕ)^1024*2500000000000000^4453 ≤ 2500071476130389^4453*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006216766504081113 50000000000000000000 2500071476130389 2500000000000000 1024 4453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500071476130389/2500000000000000 : ℝ)) (X := (50006216766504081113/50000000000000000000 : ℝ)) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12504517437699840183/12500000000000000000 : ℝ) ≤ (2000166187745001/2000000000000000 : ℝ) ^ (4453/1024 : ℝ) := by
    have hpowers : (12504517437699840183/12500000000000000000 : ℝ)^1024 ≤ (2000166187745001/2000000000000000 : ℝ)^4453 := by
      have hnat : (12504517437699840183 : ℕ)^1024*2000000000000000^4453 ≤ 2000166187745001^4453*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504517437699840183 12500000000000000000 2000166187745001 2000000000000000 1024 4453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000166187745001/2000000000000000 : ℝ)) (X := (12504517437699840183/12500000000000000000 : ℝ)) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029922735094640351/50000000000000000000 : ℝ) ≤ (5000687986464227/5000000000000000 : ℝ) ^ (4453/1024 : ℝ) := by
    have hpowers : (50029922735094640351/50000000000000000000 : ℝ)^1024 ≤ (5000687986464227/5000000000000000 : ℝ)^4453 := by
      have hnat : (50029922735094640351 : ℕ)^1024*5000000000000000^4453 ≤ 5000687986464227^4453*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029922735094640351 50000000000000000000 5000687986464227 5000000000000000 1024 4453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000687986464227/5000000000000000 : ℝ)) (X := (50029922735094640351/50000000000000000000 : ℝ)) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6216766504081113/100000000000000000000 : ℝ) ≤ ((5864948579044561009/5866250000000000000 : ℝ)+2*(545034203449/469300000000000 : ℝ)*(5391/50000 : ℝ))^(4453/1024 : ℝ) := by
    rw [show (5864948579044561009/5866250000000000000 : ℝ)+2*(545034203449/469300000000000 : ℝ)*(5391/50000 : ℝ)=(2500071476130389/2500000000000000 : ℝ) by norm_num, show 1+2*(6216766504081113/100000000000000000000 : ℝ)=(50006216766504081113/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29922735094640351/100000000000000000000 : ℝ)+(6216766504081113/100000000000000000000 : ℝ) ≤ ((5864948579044561009/5866250000000000000 : ℝ)+(545034203449/469300000000000 : ℝ)*((619/4000 : ℝ)+(5391/50000 : ℝ)))^(4453/1024 : ℝ) := by
    rw [show (5864948579044561009/5866250000000000000 : ℝ)+(545034203449/469300000000000 : ℝ)*((619/4000 : ℝ)+(5391/50000 : ℝ))=(2000166187745001/2000000000000000 : ℝ) by norm_num, show 1+(29922735094640351/100000000000000000000 : ℝ)+(6216766504081113/100000000000000000000 : ℝ)=(12504517437699840183/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29922735094640351/100000000000000000000 : ℝ) ≤ ((5864948579044561009/5866250000000000000 : ℝ)+2*(545034203449/469300000000000 : ℝ)*(619/4000 : ℝ))^(4453/1024 : ℝ) := by
    rw [show (5864948579044561009/5866250000000000000 : ℝ)+2*(545034203449/469300000000000 : ℝ)*(619/4000 : ℝ)=(5000687986464227/5000000000000000 : ℝ) by norm_num, show 1+2*(29922735094640351/100000000000000000000 : ℝ)=(50029922735094640351/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5864948579044561009/5866250000000000000 : ℝ)*(X 1 0+X 2 0)+(545034203449/469300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4453/1024 : ℝ)) (lo := (5391/50000 : ℝ)) (hi := (619/4000 : ℝ)) (c := (5864948579044561009/5866250000000000000 : ℝ)) (alpha := (545034203449/469300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5864948579044561009/5866250000000000000 : ℝ)*(X 0 1+X 2 1)+(545034203449/469300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4453/1024 : ℝ)) (lo := (5391/50000 : ℝ)) (hi := (619/4000 : ℝ)) (c := (5864948579044561009/5866250000000000000 : ℝ)) (alpha := (545034203449/469300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5864948579044561009/5866250000000000000 : ℝ)*(X 0 2+X 1 2)+(545034203449/469300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4453/1024 : ℝ)) (lo := (5391/50000 : ℝ)) (hi := (619/4000 : ℝ)) (c := (5864948579044561009/5866250000000000000 : ℝ)) (alpha := (545034203449/469300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-169816999/1000000000 : ℝ)*X 0 0+(54064089/100000000 : ℝ)*X 0 1+(5406409581/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5270211949/10000000000 : ℝ)*X 1 0+(-471705277/2500000000 : ℝ)*X 1 1+(5406409309/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2635105967/5000000000 : ℝ)*X 2 0+(5406408469/10000000000 : ℝ)*X 2 1+(-943411139/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2245021781/5000000000 : ℝ)*X 0 0+(2095135879/5000000000 : ℝ)*X 0 1+(1047567803/2500000000 : ℝ)*X 0 2+(2245021781/5000000000 : ℝ)*X 1 0+(2095135879/5000000000 : ℝ)*X 1 1+(1047567803/2500000000 : ℝ)*X 1 2+(2245021781/5000000000 : ℝ)*X 2 0+(2095135879/5000000000 : ℝ)*X 2 1+(1047567803/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-535771011/2500000000 : ℝ)*X 0 0+(81912419/156250000 : ℝ)*X 0 1+(2621197637/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2692348493/5000000000 : ℝ)*X 1 0+(-244242887/1250000000 : ℝ)*X 1 1+(262119767/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((134617429/250000000 : ℝ)*X 2 0+(52423951/100000000 : ℝ)*X 2 1+(-1953943183/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4078485813/10000000000 : ℝ)*X 0 0+(1098977871/2500000000 : ℝ)*X 0 1+(549488951/1250000000 : ℝ)*X 0 2+(4078485813/10000000000 : ℝ)*X 1 0+(1098977871/2500000000 : ℝ)*X 1 1+(549488951/1250000000 : ℝ)*X 1 2+(4078485813/10000000000 : ℝ)*X 2 0+(1098977871/2500000000 : ℝ)*X 2 1+(549488951/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2049253529/10000000000 : ℝ)*X 0 0+(5127866949/10000000000 : ℝ)*X 0 1+(5426956861/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((525586137/1000000000 : ℝ)*X 1 0+(-1878158003/10000000000 : ℝ)*X 1 1+(2713478333/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5255861391/10000000000 : ℝ)*X 2 0+(2713478583/5000000000 : ℝ)*X 2 1+(-1878157287/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4540449979/10000000000 : ℝ)*X 0 0+(1041119183/2500000000 : ℝ)*X 0 1+(1041119023/2500000000 : ℝ)*X 0 2+(4540449979/10000000000 : ℝ)*X 1 0+(1041119183/2500000000 : ℝ)*X 1 1+(1041119023/2500000000 : ℝ)*X 1 2+(4540449979/10000000000 : ℝ)*X 2 0+(1041119183/2500000000 : ℝ)*X 2 1+(1041119023/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1792138347/10000000000 : ℝ)*X 0 0+(344820967/625000000 : ℝ)*X 0 1+(1306850897/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5395160237/10000000000 : ℝ)*X 1 0+(-1959894623/10000000000 : ℝ)*X 1 1+(5227403569/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((337197517/625000000 : ℝ)*X 2 0+(2613701741/5000000000 : ℝ)*X 2 1+(-489973673/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4040009351/10000000000 : ℝ)*X 0 0+(2207342987/5000000000 : ℝ)*X 0 1+(4414685463/10000000000 : ℝ)*X 0 2+(4040009351/10000000000 : ℝ)*X 1 0+(2207342987/5000000000 : ℝ)*X 1 1+(4414685463/10000000000 : ℝ)*X 1 2+(4040009351/10000000000 : ℝ)*X 2 0+(2207342987/5000000000 : ℝ)*X 2 1+(4414685463/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-63701/100000 : ℝ) ≤ (-18683573476736094596436232936539/29331250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22874221/100000000000000 : ℝ)*(lower3) + (8361861/100000000000000 : ℝ)*(lower4) + (272631/10000000000000 : ℝ)*(upper5) + (434845369914557/20000000000000 : ℝ)*(major0) + (434845369914557/20000000000000 : ℝ)*(major1) + (434845369914557/20000000000000 : ℝ)*(major2) + (1152875329/50000000000000 : ℝ)*(sp2) + (754278121388643/25000000000000 : ℝ)*(sp4) + (3017083945127163/100000000000000 : ℝ)*(sp5) + (1508557287923981/50000000000000 : ℝ)*(sp6) + (270510616232147/20000000000000 : ℝ)*(sp7) + (274752753/6250000000000 : ℝ)*(sp12) + (1029264733/3125000000000 : ℝ)*(sp13) + (16577896811/100000000000000 : ℝ)*(sp15) + (676284829528773/50000000000000 : ℝ)*(f.failure) + (3017116881598619/100000000000000 : ℝ)*(f.sum) + (7083126814563/4693000000000000000000000000 : ℝ)*base66 + (369557629293220513/117325000000000000000000000000000 : ℝ)*base67 + (63562656663254487/117325000000000000000000000000000 : ℝ)*base70 + (226423599688420513/117325000000000000000000000000000 : ℝ)*base71 + (19069847475919/4693000000000000000000000000 : ℝ)*base73 + (718231315564845513/117325000000000000000000000000000 : ℝ)*base75 + (261197004776270513/117325000000000000000000000000000 : ℝ)*base77 + (98051224892170513/117325000000000000000000000000000 : ℝ)*base79 + (9229746195907/2346500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (6836071/1000000000000000000000 : ℝ)*base90 + (6836071/1000000000000000000000 : ℝ)*base92 + (6836071/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58473/100000 : ℝ) ≤ (42879034480633566429978560429013/73328125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (228748737/100000000000000 : ℝ)*(lower0) + (926513/10000000000000 : ℝ)*(upper1) + (334197151/100000000000000 : ℝ)*(upper2) + (562054860394519/25000000000000 : ℝ)*(major0) + (562054860394519/25000000000000 : ℝ)*(major1) + (562054860394519/25000000000000 : ℝ)*(major2) + (1539170383563687/50000000000000 : ℝ)*(sp0) + (1539172361864223/50000000000000 : ℝ)*(sp1) + (153906843004451/5000000000000 : ℝ)*(sp2) + (1398595052218967/100000000000000 : ℝ)*(sp3) + (2428212869/100000000000000 : ℝ)*(sp5) + (42058370459/20000000000000 : ℝ)*(sp10) + (4824412723/100000000000000 : ℝ)*(sp11) + (6384813941/100000000000000 : ℝ)*(sp12) + (139859987663169/10000000000000 : ℝ)*(f.failure) + (615669430388263/20000000000000 : ℝ)*(f.sum) + (10805782022629/1466562500000000000000000000 : ℝ)*base65 + (456131130925590329/146656250000000000000000000000000 : ℝ)*base68 + (227998548494284671/146656250000000000000000000000000 : ℝ)*base69 + (423661200325746579/146656250000000000000000000000000 : ℝ)*base72 + (21778673795587/11732500000000000000000000000 : ℝ)*base73 + (370262696902465329/146656250000000000000000000000000 : ℝ)*base76 + (506067132382347171/146656250000000000000000000000000 : ℝ)*base77 + (653715611313527829/146656250000000000000000000000000 : ℝ)*base80 + (75072469536949/23465000000000000000000000000 : ℝ)*base81 + (823163/200000000000000000000 : ℝ)*base90 + (823163/200000000000000000000 : ℝ)*base92 + (823163/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (79957/100000 : ℝ) ≤ (58632616625732258697790301629149/73328125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (54246217/50000000000000 : ℝ)*(lower3) + (108164631/50000000000000 : ℝ)*(upper4) + (46431701/50000000000000 : ℝ)*(lower5) + (152864875336551/6250000000000 : ℝ)*(major0) + (152864875336551/6250000000000 : ℝ)*(major1) + (152864875336551/6250000000000 : ℝ)*(major2) + (986040391/20000000000000 : ℝ)*(sp0) + (6500188769/25000000000000 : ℝ)*(sp1) + (171854494011/100000000000000 : ℝ)*(sp2) + (43897141111/50000000000000 : ℝ)*(sp3) + (835870286460093/25000000000000 : ℝ)*(sp8) + (3343460075287251/100000000000000 : ℝ)*(sp9) + (835828555387079/25000000000000 : ℝ)*(sp10) + (190181132261893/12500000000000 : ℝ)*(sp11) + (304307370475473/20000000000000 : ℝ)*(f.failure) + (3343486076042327/100000000000000 : ℝ)*(f.sum) + (35074277247023/11732500000000000000000000000 : ℝ)*base66 + (283394917196903791/36664062500000000000000000000000 : ℝ)*base68 + (961931139833979457/73328125000000000000000000000000 : ℝ)*base70 + (81699582538964229/9166015625000000000000000000000 : ℝ)*base72 + (145990887350189/23465000000000000000000000000 : ℝ)*base73 + (210813208210756583/18332031250000000000000000000000 : ℝ)*base76 + (234292756657412833/18332031250000000000000000000000 : ℝ)*base78 + (654310404382729457/73328125000000000000000000000000 : ℝ)*base80 + (14624814966527/11732500000000000000000000000 : ℝ)*base81 + (76971/400000000000000000000 : ℝ)*base90 + (76971/400000000000000000000 : ℝ)*base92 + (76971/400000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-85787/100000 : ℝ) ≤ (-15726042501153325887782690781177/18332031250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1327231/6250000000000 : ℝ)*(lower0) + (46332263/100000000000000 : ℝ)*(lower2) + (88142789/100000000000000 : ℝ)*(upper3) + (1132729/5000000000000 : ℝ)*(lower4) + (310513917894991/12500000000000 : ℝ)*(major0) + (310513917894991/12500000000000 : ℝ)*(major1) + (310513917894991/12500000000000 : ℝ)*(major2) + (1774661107/50000000000000 : ℝ)*(sp0) + (105548289611/100000000000000 : ℝ)*(sp5) + (47232740827/50000000000000 : ℝ)*(sp6) + (3451467573482473/100000000000000 : ℝ)*(sp12) + (138054622980603/4000000000000 : ℝ)*(sp13) + (3451376657323033/100000000000000 : ℝ)*(sp14) + (386336599736477/25000000000000 : ℝ)*(sp15) + (386336599736477/25000000000000 : ℝ)*(f.failure) + (1725735561402343/50000000000000 : ℝ)*(f.sum) + (62627361407733/23465000000000000000000000000 : ℝ)*base66 + (1038145255759006581/73328125000000000000000000000000 : ℝ)*base68 + (1041862963391850331/73328125000000000000000000000000 : ℝ)*base70 + (437568038605542353/36664062500000000000000000000000 : ℝ)*base72 + (87806275371443/23465000000000000000000000000 : ℝ)*base74 + (138284035020622739/18332031250000000000000000000000 : ℝ)*base76 + (642991141581944081/73328125000000000000000000000000 : ℝ)*base78 + (1073094133084787831/73328125000000000000000000000000 : ℝ)*base80 + (38443452541659/11732500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (8074321/500000000000000000000 : ℝ)*base89 + (8074321/500000000000000000000 : ℝ)*base91 + (8074321/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1479_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32149573/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (619/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5391/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63701/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58473/100000 : ℝ) else (79957/100000 : ℝ) ≤ X j i ∧ X j i ≤ (85787/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1479_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1479_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32149573/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15477/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (539/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63701/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58473/100000 : ℝ) else (79957/100000 : ℝ) ≤ X j i ∧ X j i ≤ (85787/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1479_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1479_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32149573/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15477/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (539/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63701/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58473/100000 : ℝ) else (79957/100000 : ℝ) ≤ X j i ∧ X j i ≤ (85787/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1479_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

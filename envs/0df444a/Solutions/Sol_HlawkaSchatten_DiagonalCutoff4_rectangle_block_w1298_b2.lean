-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1298_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:35:57.703592+00:00
-- url     : https://prove2.me/submissions/49c059fd-2e68-44ba-9786-ddae17d4fd90

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
theorem support_rectangle_w1298_s6_0 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-260324379/1250000000 : ℝ)*x 0 + (108300197/200000000 : ℝ)*x 1 + (5243123927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (260324379/1250000000 : ℝ)^2129 ≤ (6336081638039/50000000000000 : ℝ)^1617 := by
    have hnat : (260324379 : ℕ)^2129*50000000000000^1617 ≤ 6336081638039^1617*1250000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260324379 1250000000 6336081638039 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108300197/200000000 : ℝ)^2129 ≤ (8918200806697/20000000000000 : ℝ)^1617 := by
    have hnat : (108300197 : ℕ)^2129*20000000000000^1617 ≤ 8918200806697^1617*200000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108300197 200000000 8918200806697 20000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243123927/10000000000 : ℝ)^2129 ≤ (42736832674459/100000000000000 : ℝ)^1617 := by
    have hnat : (5243123927 : ℕ)^2129*100000000000000^1617 ≤ 42736832674459^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243123927 10000000000 42736832674459 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-260324379/1250000000 : ℝ), (108300197/200000000 : ℝ), (5243123927/10000000000 : ℝ)] ![(6336081638039/50000000000000 : ℝ), (8918200806697/20000000000000 : ℝ), (42736832674459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-260324379/1250000000 : ℝ)|^2129 ≤ (6336081638039/50000000000000 : ℝ)^1617
        have hw : |(-260324379/1250000000 : ℝ)|=(260324379/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108300197/200000000 : ℝ)|^2129 ≤ (8918200806697/20000000000000 : ℝ)^1617
        have hw : |(108300197/200000000 : ℝ)|=(108300197/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243123927/10000000000 : ℝ)|^2129 ≤ (42736832674459/100000000000000 : ℝ)^1617
        have hw : |(5243123927/10000000000 : ℝ)|=(5243123927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s6_1 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674858713/5000000000 : ℝ)*x 0 + (-2170209693/10000000000 : ℝ)*x 1 + (655390491/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674858713/5000000000 : ℝ)^2129 ≤ (43884451750091/100000000000000 : ℝ)^1617 := by
    have hnat : (2674858713 : ℕ)^2129*100000000000000^1617 ≤ 43884451750091^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674858713 5000000000 43884451750091 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2170209693/10000000000 : ℝ)^2129 ≤ (1672339442687/12500000000000 : ℝ)^1617 := by
    have hnat : (2170209693 : ℕ)^2129*12500000000000^1617 ≤ 1672339442687^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170209693 10000000000 1672339442687 12500000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655390491/1250000000 : ℝ)^2129 ≤ (42736832685191/100000000000000 : ℝ)^1617 := by
    have hnat : (655390491 : ℕ)^2129*100000000000000^1617 ≤ 42736832685191^1617*1250000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655390491 1250000000 42736832685191 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674858713/5000000000 : ℝ), (-2170209693/10000000000 : ℝ), (655390491/1250000000 : ℝ)] ![(43884451750091/100000000000000 : ℝ), (1672339442687/12500000000000 : ℝ), (42736832685191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674858713/5000000000 : ℝ)|^2129 ≤ (43884451750091/100000000000000 : ℝ)^1617
        have hw : |(2674858713/5000000000 : ℝ)|=(2674858713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2170209693/10000000000 : ℝ)|^2129 ≤ (1672339442687/12500000000000 : ℝ)^1617
        have hw : |(-2170209693/10000000000 : ℝ)|=(2170209693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655390491/1250000000 : ℝ)|^2129 ≤ (42736832685191/100000000000000 : ℝ)^1617
        have hw : |(655390491/1250000000 : ℝ)|=(655390491/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s6_2 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1337429357/2500000000 : ℝ)*x 0 + (2621561963/5000000000 : ℝ)*x 1 + (-1085104847/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337429357/2500000000 : ℝ)^2129 ≤ (10971112942923/25000000000000 : ℝ)^1617 := by
    have hnat : (1337429357 : ℕ)^2129*25000000000000^1617 ≤ 10971112942923^1617*2500000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337429357 2500000000 10971112942923 25000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621561963/5000000000 : ℝ)^2129 ≤ (42736832663727/100000000000000 : ℝ)^1617 := by
    have hnat : (2621561963 : ℕ)^2129*100000000000000^1617 ≤ 42736832663727^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621561963 5000000000 42736832663727 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085104847/5000000000 : ℝ)^2129 ≤ (3344678887403/25000000000000 : ℝ)^1617 := by
    have hnat : (1085104847 : ℕ)^2129*25000000000000^1617 ≤ 3344678887403^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085104847 5000000000 3344678887403 25000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337429357/2500000000 : ℝ), (2621561963/5000000000 : ℝ), (-1085104847/5000000000 : ℝ)] ![(10971112942923/25000000000000 : ℝ), (42736832663727/100000000000000 : ℝ), (3344678887403/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337429357/2500000000 : ℝ)|^2129 ≤ (10971112942923/25000000000000 : ℝ)^1617
        have hw : |(1337429357/2500000000 : ℝ)|=(1337429357/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621561963/5000000000 : ℝ)|^2129 ≤ (42736832663727/100000000000000 : ℝ)^1617
        have hw : |(2621561963/5000000000 : ℝ)|=(2621561963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1085104847/5000000000 : ℝ)|^2129 ≤ (3344678887403/25000000000000 : ℝ)^1617
        have hw : |(-1085104847/5000000000 : ℝ)|=(1085104847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s6_3 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1084563311/2500000000 : ℝ)*x 0 + (4164658649/10000000000 : ℝ)*x 1 + (2259367539/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1084563311/2500000000 : ℝ)^2129 ≤ (33302423040863/100000000000000 : ℝ)^1617 := by
    have hnat : (1084563311 : ℕ)^2129*100000000000000^1617 ≤ 33302423040863^1617*2500000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084563311 2500000000 33302423040863 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4164658649/10000000000 : ℝ)^2129 ≤ (15779551617259/50000000000000 : ℝ)^1617 := by
    have hnat : (4164658649 : ℕ)^2129*50000000000000^1617 ≤ 15779551617259^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4164658649 10000000000 15779551617259 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2259367539/5000000000 : ℝ)^2129 ≤ (878461842743/2500000000000 : ℝ)^1617 := by
    have hnat : (2259367539 : ℕ)^2129*2500000000000^1617 ≤ 878461842743^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259367539 5000000000 878461842743 2500000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1084563311/2500000000 : ℝ), (4164658649/10000000000 : ℝ), (2259367539/5000000000 : ℝ)] ![(33302423040863/100000000000000 : ℝ), (15779551617259/50000000000000 : ℝ), (878461842743/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1084563311/2500000000 : ℝ)|^2129 ≤ (33302423040863/100000000000000 : ℝ)^1617
        have hw : |(1084563311/2500000000 : ℝ)|=(1084563311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4164658649/10000000000 : ℝ)|^2129 ≤ (15779551617259/50000000000000 : ℝ)^1617
        have hw : |(4164658649/10000000000 : ℝ)|=(4164658649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2259367539/5000000000 : ℝ)|^2129 ≤ (878461842743/2500000000000 : ℝ)^1617
        have hw : |(2259367539/5000000000 : ℝ)|=(2259367539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s6_4 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2082607739/10000000000 : ℝ)*x 0 + (5243737251/10000000000 : ℝ)*x 1 + (2707196673/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2082607739/10000000000 : ℝ)^2129 ≤ (792016567361/6250000000000 : ℝ)^1617 := by
    have hnat : (2082607739 : ℕ)^2129*6250000000000^1617 ≤ 792016567361^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082607739 10000000000 792016567361 6250000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243737251/10000000000 : ℝ)^2129 ≤ (4274341494689/10000000000000 : ℝ)^1617 := by
    have hnat : (5243737251 : ℕ)^2129*10000000000000^1617 ≤ 4274341494689^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243737251 10000000000 4274341494689 10000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707196673/5000000000 : ℝ)^2129 ≤ (1114607998809/2500000000000 : ℝ)^1617 := by
    have hnat : (2707196673 : ℕ)^2129*2500000000000^1617 ≤ 1114607998809^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707196673 5000000000 1114607998809 2500000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2082607739/10000000000 : ℝ), (5243737251/10000000000 : ℝ), (2707196673/5000000000 : ℝ)] ![(792016567361/6250000000000 : ℝ), (4274341494689/10000000000000 : ℝ), (1114607998809/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2082607739/10000000000 : ℝ)|^2129 ≤ (792016567361/6250000000000 : ℝ)^1617
        have hw : |(-2082607739/10000000000 : ℝ)|=(2082607739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243737251/10000000000 : ℝ)|^2129 ≤ (4274341494689/10000000000000 : ℝ)^1617
        have hw : |(5243737251/10000000000 : ℝ)|=(5243737251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707196673/5000000000 : ℝ)|^2129 ≤ (1114607998809/2500000000000 : ℝ)^1617
        have hw : |(2707196673/5000000000 : ℝ)|=(2707196673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s6_5 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (165802407/312500000 : ℝ)*x 0 + (-1998940509/10000000000 : ℝ)*x 1 + (216575723/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165802407/312500000 : ℝ)^2129 ≤ (1085235318079/2500000000000 : ℝ)^1617 := by
    have hnat : (165802407 : ℕ)^2129*2500000000000^1617 ≤ 1085235318079^1617*312500000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165802407 312500000 1085235318079 2500000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1998940509/10000000000 : ℝ)^2129 ≤ (6003135124763/50000000000000 : ℝ)^1617 := by
    have hnat : (1998940509 : ℕ)^2129*50000000000000^1617 ≤ 6003135124763^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1998940509 10000000000 6003135124763 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216575723/400000000 : ℝ)^2129 ≤ (2786519813391/6250000000000 : ℝ)^1617 := by
    have hnat : (216575723 : ℕ)^2129*6250000000000^1617 ≤ 2786519813391^1617*400000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216575723 400000000 2786519813391 6250000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165802407/312500000 : ℝ), (-1998940509/10000000000 : ℝ), (216575723/400000000 : ℝ)] ![(1085235318079/2500000000000 : ℝ), (6003135124763/50000000000000 : ℝ), (2786519813391/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165802407/312500000 : ℝ)|^2129 ≤ (1085235318079/2500000000000 : ℝ)^1617
        have hw : |(165802407/312500000 : ℝ)|=(165802407/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1998940509/10000000000 : ℝ)|^2129 ≤ (6003135124763/50000000000000 : ℝ)^1617
        have hw : |(-1998940509/10000000000 : ℝ)|=(1998940509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216575723/400000000 : ℝ)|^2129 ≤ (2786519813391/6250000000000 : ℝ)^1617
        have hw : |(216575723/400000000 : ℝ)|=(216575723/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s6_6 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (165802403/312500000 : ℝ)*x 0 + (338399569/625000000 : ℝ)*x 1 + (-499735161/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165802403/312500000 : ℝ)^2129 ≤ (2713088209019/6250000000000 : ℝ)^1617 := by
    have hnat : (165802403 : ℕ)^2129*6250000000000^1617 ≤ 2713088209019^1617*312500000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165802403 312500000 2713088209019 6250000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338399569/625000000 : ℝ)^2129 ≤ (8916863465733/20000000000000 : ℝ)^1617 := by
    have hnat : (338399569 : ℕ)^2129*20000000000000^1617 ≤ 8916863465733^1617*625000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338399569 625000000 8916863465733 20000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (499735161/2500000000 : ℝ)^2129 ≤ (3001567829281/25000000000000 : ℝ)^1617 := by
    have hnat : (499735161 : ℕ)^2129*25000000000000^1617 ≤ 3001567829281^1617*2500000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499735161 2500000000 3001567829281 25000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165802403/312500000 : ℝ), (338399569/625000000 : ℝ), (-499735161/2500000000 : ℝ)] ![(2713088209019/6250000000000 : ℝ), (8916863465733/20000000000000 : ℝ), (3001567829281/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165802403/312500000 : ℝ)|^2129 ≤ (2713088209019/6250000000000 : ℝ)^1617
        have hw : |(165802403/312500000 : ℝ)|=(165802403/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338399569/625000000 : ℝ)|^2129 ≤ (8916863465733/20000000000000 : ℝ)^1617
        have hw : |(338399569/625000000 : ℝ)|=(338399569/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-499735161/2500000000 : ℝ)|^2129 ≤ (3001567829281/25000000000000 : ℝ)^1617
        have hw : |(-499735161/2500000000 : ℝ)|=(499735161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s6_7 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4338279587/10000000000 : ℝ)*x 0 + (4517471309/10000000000 : ℝ)*x 1 + (416592869/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4338279587/10000000000 : ℝ)^2129 ≤ (16651344646231/50000000000000 : ℝ)^1617 := by
    have hnat : (4338279587 : ℕ)^2129*50000000000000^1617 ≤ 16651344646231^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4338279587 10000000000 16651344646231 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4517471309/10000000000 : ℝ)^2129 ≤ (3512553532319/10000000000000 : ℝ)^1617 := by
    have hnat : (4517471309 : ℕ)^2129*10000000000000^1617 ≤ 3512553532319^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4517471309 10000000000 3512553532319 10000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (416592869/1000000000 : ℝ)^2129 ≤ (31571775363709/100000000000000 : ℝ)^1617 := by
    have hnat : (416592869 : ℕ)^2129*100000000000000^1617 ≤ 31571775363709^1617*1000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416592869 1000000000 31571775363709 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4338279587/10000000000 : ℝ), (4517471309/10000000000 : ℝ), (416592869/1000000000 : ℝ)] ![(16651344646231/50000000000000 : ℝ), (3512553532319/10000000000000 : ℝ), (31571775363709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4338279587/10000000000 : ℝ)|^2129 ≤ (16651344646231/50000000000000 : ℝ)^1617
        have hw : |(4338279587/10000000000 : ℝ)|=(4338279587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4517471309/10000000000 : ℝ)|^2129 ≤ (3512553532319/10000000000000 : ℝ)^1617
        have hw : |(4517471309/10000000000 : ℝ)|=(4517471309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(416592869/1000000000 : ℝ)|^2129 ≤ (31571775363709/100000000000000 : ℝ)^1617
        have hw : |(416592869/1000000000 : ℝ)|=(416592869/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1298_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76498753/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1469/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1103/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (11041/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14679/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1469/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1103/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1469/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1103/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1469/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1103/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1469/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1103/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1469/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1103/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1469/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1103/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1103/10000 : ℝ) ^ (4257/1024 : ℝ) ≤ (10465729091998183/100000000000000000000 : ℝ) := by
    have hpowers : (1103/10000 : ℝ)^4257 ≤ (10465729091998183/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1103 : ℕ)^4257*100000000000000000000^1024 ≤ 10465729091998183^1024*10000^4257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1103 10000 10465729091998183 100000000000000000000 4257 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1103/10000 : ℝ)) (X := (10465729091998183/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1469/10000 : ℝ) ^ (4257/1024 : ℝ) ≤ (3444457920095107/10000000000000000000 : ℝ) := by
    have hpowers : (1469/10000 : ℝ)^4257 ≤ (3444457920095107/10000000000000000000 : ℝ)^1024 := by
      have hnat : (1469 : ℕ)^4257*10000000000000000000^1024 ≤ 3444457920095107^1024*10000^4257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1469 10000 3444457920095107 10000000000000000000 4257 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1469/10000 : ℝ)) (X := (3444457920095107/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010465729091998183/50000000000000000000 : ℝ) ≤ (5000251727857369/5000000000000000 : ℝ) ^ (4257/1024 : ℝ) := by
    have hpowers : (50010465729091998183/50000000000000000000 : ℝ)^1024 ≤ (5000251727857369/5000000000000000 : ℝ)^4257 := by
      have hnat : (50010465729091998183 : ℕ)^1024*5000000000000000^4257 ≤ 5000251727857369^4257*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010465729091998183 50000000000000000000 5000251727857369 5000000000000000 1024 4257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000251727857369/5000000000000000 : ℝ)) (X := (50010465729091998183/50000000000000000000 : ℝ)) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044910308292949253/100000000000000000000 : ℝ) ≤ (10001080110760733/10000000000000000 : ℝ) ^ (4257/1024 : ℝ) := by
    have hpowers : (100044910308292949253/100000000000000000000 : ℝ)^1024 ≤ (10001080110760733/10000000000000000 : ℝ)^4257 := by
      have hnat : (100044910308292949253 : ℕ)^1024*10000000000000000^4257 ≤ 10001080110760733^4257*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044910308292949253 100000000000000000000 10001080110760733 10000000000000000 1024 4257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001080110760733/10000000000000000 : ℝ)) (X := (100044910308292949253/100000000000000000000 : ℝ)) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003444457920095107/5000000000000000000 : ℝ) ≤ (1250207095725841/1250000000000000 : ℝ) ^ (4257/1024 : ℝ) := by
    have hpowers : (5003444457920095107/5000000000000000000 : ℝ)^1024 ≤ (1250207095725841/1250000000000000 : ℝ)^4257 := by
      have hnat : (5003444457920095107 : ℕ)^1024*1250000000000000^4257 ≤ 1250207095725841^4257*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003444457920095107 5000000000000000000 1250207095725841 1250000000000000 1024 4257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250207095725841/1250000000000000 : ℝ)) (X := (5003444457920095107/5000000000000000000 : ℝ)) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10465729091998183/100000000000000000000 : ℝ) ≤ ((609818693960021523/610000000000000000 : ℝ)+2*(38443669733/24400000000000 : ℝ)*(1103/10000 : ℝ))^(4257/1024 : ℝ) := by
    rw [show (609818693960021523/610000000000000000 : ℝ)+2*(38443669733/24400000000000 : ℝ)*(1103/10000 : ℝ)=(5000251727857369/5000000000000000 : ℝ) by norm_num, show 1+2*(10465729091998183/100000000000000000000 : ℝ)=(50010465729091998183/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3444457920095107/10000000000000000000 : ℝ)+(10465729091998183/100000000000000000000 : ℝ) ≤ ((609818693960021523/610000000000000000 : ℝ)+(38443669733/24400000000000 : ℝ)*((1469/10000 : ℝ)+(1103/10000 : ℝ)))^(4257/1024 : ℝ) := by
    rw [show (609818693960021523/610000000000000000 : ℝ)+(38443669733/24400000000000 : ℝ)*((1469/10000 : ℝ)+(1103/10000 : ℝ))=(10001080110760733/10000000000000000 : ℝ) by norm_num, show 1+(3444457920095107/10000000000000000000 : ℝ)+(10465729091998183/100000000000000000000 : ℝ)=(100044910308292949253/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3444457920095107/10000000000000000000 : ℝ) ≤ ((609818693960021523/610000000000000000 : ℝ)+2*(38443669733/24400000000000 : ℝ)*(1469/10000 : ℝ))^(4257/1024 : ℝ) := by
    rw [show (609818693960021523/610000000000000000 : ℝ)+2*(38443669733/24400000000000 : ℝ)*(1469/10000 : ℝ)=(1250207095725841/1250000000000000 : ℝ) by norm_num, show 1+2*(3444457920095107/10000000000000000000 : ℝ)=(5003444457920095107/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (609818693960021523/610000000000000000 : ℝ)*(X 1 0+X 2 0)+(38443669733/24400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4257/1024 : ℝ)) (lo := (1103/10000 : ℝ)) (hi := (1469/10000 : ℝ)) (c := (609818693960021523/610000000000000000 : ℝ)) (alpha := (38443669733/24400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (609818693960021523/610000000000000000 : ℝ)*(X 0 1+X 2 1)+(38443669733/24400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4257/1024 : ℝ)) (lo := (1103/10000 : ℝ)) (hi := (1469/10000 : ℝ)) (c := (609818693960021523/610000000000000000 : ℝ)) (alpha := (38443669733/24400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (609818693960021523/610000000000000000 : ℝ)*(X 0 2+X 1 2)+(38443669733/24400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4257/1024 : ℝ)) (lo := (1103/10000 : ℝ)) (hi := (1469/10000 : ℝ)) (c := (609818693960021523/610000000000000000 : ℝ)) (alpha := (38443669733/24400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-260324379/1250000000 : ℝ)*X 0 0+(108300197/200000000 : ℝ)*X 0 1+(5243123927/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674858713/5000000000 : ℝ)*X 1 0+(-2170209693/10000000000 : ℝ)*X 1 1+(655390491/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337429357/2500000000 : ℝ)*X 2 0+(2621561963/5000000000 : ℝ)*X 2 1+(-1085104847/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1084563311/2500000000 : ℝ)*X 0 0+(4164658649/10000000000 : ℝ)*X 0 1+(2259367539/5000000000 : ℝ)*X 0 2+(1084563311/2500000000 : ℝ)*X 1 0+(4164658649/10000000000 : ℝ)*X 1 1+(2259367539/5000000000 : ℝ)*X 1 2+(1084563311/2500000000 : ℝ)*X 2 0+(4164658649/10000000000 : ℝ)*X 2 1+(2259367539/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2082607739/10000000000 : ℝ)*X 0 0+(5243737251/10000000000 : ℝ)*X 0 1+(2707196673/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((165802407/312500000 : ℝ)*X 1 0+(-1998940509/10000000000 : ℝ)*X 1 1+(216575723/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((165802403/312500000 : ℝ)*X 2 0+(338399569/625000000 : ℝ)*X 2 1+(-499735161/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4338279587/10000000000 : ℝ)*X 0 0+(4517471309/10000000000 : ℝ)*X 0 1+(416592869/1000000000 : ℝ)*X 0 2+(4338279587/10000000000 : ℝ)*X 1 0+(4517471309/10000000000 : ℝ)*X 1 1+(416592869/1000000000 : ℝ)*X 1 2+(4338279587/10000000000 : ℝ)*X 2 0+(4517471309/10000000000 : ℝ)*X 2 1+(416592869/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (76915343520884954603702673/15250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (965058837/100000000000000 : ℝ)*(base19) + (901454477/100000000000000 : ℝ)*(base23) + (7038021/20000000000000 : ℝ)*(lower2) + (63769663/50000000000000 : ℝ)*(upper3) + (78397171/100000000000000 : ℝ)*(upper5) + (2160530069348339/50000000000000 : ℝ)*(major0) + (2160530069348339/50000000000000 : ℝ)*(major1) + (2160530069348339/50000000000000 : ℝ)*(major2) + (5817832367951957/100000000000000 : ℝ)*(sp0) + (5817850793919857/100000000000000 : ℝ)*(sp1) + (2908925428762109/50000000000000 : ℝ)*(sp2) + (706064536771177/25000000000000 : ℝ)*(sp3) + (19391026737/100000000000000 : ℝ)*(sp4) + (5101604487/50000000000000 : ℝ)*(sp7) + (2824268350293683/100000000000000 : ℝ)*(f.failure) + (2908925879489347/50000000000000 : ℝ)*(f.sum) + (2092839277457/610000000000000000000000000 : ℝ)*base65 + (334499880186024703/30500000000000000000000000000000 : ℝ)*base68 + (284275393851024703/30500000000000000000000000000000 : ℝ)*base70 + (176897586334524703/30500000000000000000000000000000 : ℝ)*base72 + (3416916663717/610000000000000000000000000 : ℝ)*base73 + (238433014078524703/30500000000000000000000000000000 : ℝ)*base76 + (485751054605524703/30500000000000000000000000000000 : ℝ)*base78 + (245884674831524703/30500000000000000000000000000000 : ℝ)*base80 + (1203782108367/610000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (33277299/5000000000000000000000 : ℝ)*base89 + (33277299/5000000000000000000000 : ℝ)*base91 + (33277299/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2758455860270379975939/305000000000000000000000000 : ℝ) := by norm_num
    linear_combination (346926103/20000000000000 : ℝ)*(base19) + (13792709/781250000000 : ℝ)*(base23) + (172155183/100000000000000 : ℝ)*(upper3) + (22105303/20000000000000 : ℝ)*(lower4) + (283554443/100000000000000 : ℝ)*(upper5) + (1088042599265661/25000000000000 : ℝ)*(major0) + (1088042599265661/25000000000000 : ℝ)*(major1) + (1088042599265661/25000000000000 : ℝ)*(major2) + (677996137/2500000000000 : ℝ)*(sp1) + (22768960449/100000000000000 : ℝ)*(sp2) + (2929869154353129/50000000000000 : ℝ)*(sp4) + (5859709454230263/100000000000000 : ℝ)*(sp5) + (2929856887139529/50000000000000 : ℝ)*(sp6) + (2844602183948439/100000000000000 : ℝ)*(sp7) + (2844602183948439/100000000000000 : ℝ)*(f.failure) + (2929869154353129/50000000000000 : ℝ)*(f.sum) + (622910845471/152500000000000000000000000 : ℝ)*base66 + (28797094469603297/15250000000000000000000000000000 : ℝ)*base68 + (68950513803146703/15250000000000000000000000000000 : ℝ)*base69 + (34590158878603297/15250000000000000000000000000000 : ℝ)*base72 + (650916480407/305000000000000000000000000 : ℝ)*base74 + (250280411623896703/15250000000000000000000000000000 : ℝ)*base75 + (389553435603297/15250000000000000000000000000000 : ℝ)*base78 + (96024124298396703/15250000000000000000000000000000 : ℝ)*base79 + (1203784308153/305000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (203433/5000000000000000000000 : ℝ)*base90 + (203433/5000000000000000000000 : ℝ)*base92 + (203433/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1298_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76498753/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1469/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1103/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11041/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14679/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1298_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1298_s7_0 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-416520947/2000000000 : ℝ)*x 0 + (5414912629/10000000000 : ℝ)*x 1 + (2621607451/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (416520947/2000000000 : ℝ)^2129 ≤ (6336120505657/50000000000000 : ℝ)^1617 := by
    have hnat : (416520947 : ℕ)^2129*50000000000000^1617 ≤ 6336120505657^1617*2000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416520947 2000000000 6336120505657 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414912629/10000000000 : ℝ)^2129 ≤ (44589949956111/100000000000000 : ℝ)^1617 := by
    have hnat : (5414912629 : ℕ)^2129*100000000000000^1617 ≤ 44589949956111^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414912629 10000000000 44589949956111 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621607451/5000000000 : ℝ)^2129 ≤ (21368904507259/50000000000000 : ℝ)^1617 := by
    have hnat : (2621607451 : ℕ)^2129*50000000000000^1617 ≤ 21368904507259^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621607451 5000000000 21368904507259 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-416520947/2000000000 : ℝ), (5414912629/10000000000 : ℝ), (2621607451/5000000000 : ℝ)] ![(6336120505657/50000000000000 : ℝ), (44589949956111/100000000000000 : ℝ), (21368904507259/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-416520947/2000000000 : ℝ)|^2129 ≤ (6336120505657/50000000000000 : ℝ)^1617
        have hw : |(-416520947/2000000000 : ℝ)|=(416520947/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414912629/10000000000 : ℝ)|^2129 ≤ (44589949956111/100000000000000 : ℝ)^1617
        have hw : |(5414912629/10000000000 : ℝ)|=(5414912629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621607451/5000000000 : ℝ)|^2129 ≤ (21368904507259/50000000000000 : ℝ)^1617
        have hw : |(2621607451/5000000000 : ℝ)|=(2621607451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s7_1 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674846213/5000000000 : ℝ)*x 0 + (-2170120983/10000000000 : ℝ)*x 1 + (5243216181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674846213/5000000000 : ℝ)^2129 ≤ (43884181736787/100000000000000 : ℝ)^1617 := by
    have hnat : (2674846213 : ℕ)^2129*100000000000000^1617 ≤ 43884181736787^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674846213 5000000000 43884181736787 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2170120983/10000000000 : ℝ)^2129 ≤ (535119820623/4000000000000 : ℝ)^1617 := by
    have hnat : (2170120983 : ℕ)^2129*4000000000000^1617 ≤ 535119820623^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170120983 10000000000 535119820623 4000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243216181/10000000000 : ℝ)^2129 ≤ (42737822740733/100000000000000 : ℝ)^1617 := by
    have hnat : (5243216181 : ℕ)^2129*100000000000000^1617 ≤ 42737822740733^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243216181 10000000000 42737822740733 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674846213/5000000000 : ℝ), (-2170120983/10000000000 : ℝ), (5243216181/10000000000 : ℝ)] ![(43884181736787/100000000000000 : ℝ), (535119820623/4000000000000 : ℝ), (42737822740733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674846213/5000000000 : ℝ)|^2129 ≤ (43884181736787/100000000000000 : ℝ)^1617
        have hw : |(2674846213/5000000000 : ℝ)|=(2674846213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2170120983/10000000000 : ℝ)|^2129 ≤ (535119820623/4000000000000 : ℝ)^1617
        have hw : |(-2170120983/10000000000 : ℝ)|=(2170120983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243216181/10000000000 : ℝ)|^2129 ≤ (42737822740733/100000000000000 : ℝ)^1617
        have hw : |(5243216181/10000000000 : ℝ)|=(5243216181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s7_2 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674846381/5000000000 : ℝ)*x 0 + (2621607499/5000000000 : ℝ)*x 1 + (-2170122099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674846381/5000000000 : ℝ)^2129 ≤ (10971046341441/25000000000000 : ℝ)^1617 := by
    have hnat : (2674846381 : ℕ)^2129*25000000000000^1617 ≤ 10971046341441^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674846381 5000000000 10971046341441 25000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621607499/5000000000 : ℝ)^2129 ≤ (42737810044789/100000000000000 : ℝ)^1617 := by
    have hnat : (2621607499 : ℕ)^2129*100000000000000^1617 ≤ 42737810044789^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621607499 5000000000 42737810044789 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2170122099/10000000000 : ℝ)^2129 ≤ (1672250571709/12500000000000 : ℝ)^1617 := by
    have hnat : (2170122099 : ℕ)^2129*12500000000000^1617 ≤ 1672250571709^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170122099 10000000000 1672250571709 12500000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674846381/5000000000 : ℝ), (2621607499/5000000000 : ℝ), (-2170122099/10000000000 : ℝ)] ![(10971046341441/25000000000000 : ℝ), (42737810044789/100000000000000 : ℝ), (1672250571709/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674846381/5000000000 : ℝ)|^2129 ≤ (10971046341441/25000000000000 : ℝ)^1617
        have hw : |(2674846381/5000000000 : ℝ)|=(2674846381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621607499/5000000000 : ℝ)|^2129 ≤ (42737810044789/100000000000000 : ℝ)^1617
        have hw : |(2621607499/5000000000 : ℝ)|=(2621607499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2170122099/10000000000 : ℝ)|^2129 ≤ (1672250571709/12500000000000 : ℝ)^1617
        have hw : |(-2170122099/10000000000 : ℝ)|=(2170122099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s7_3 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (867651921/2000000000 : ℝ)*x 0 + (1041213169/2500000000 : ℝ)*x 1 + (2259269859/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (867651921/2000000000 : ℝ)^2129 ≤ (33302487332143/100000000000000 : ℝ)^1617 := by
    have hnat : (867651921 : ℕ)^2129*100000000000000^1617 ≤ 33302487332143^1617*2000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      867651921 2000000000 33302487332143 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1041213169/2500000000 : ℝ)^2129 ≤ (31561039104817/100000000000000 : ℝ)^1617 := by
    have hnat : (1041213169 : ℕ)^2129*100000000000000^1617 ≤ 31561039104817^1617*2500000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041213169 2500000000 31561039104817 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2259269859/5000000000 : ℝ)^2129 ≤ (7027294710321/20000000000000 : ℝ)^1617 := by
    have hnat : (2259269859 : ℕ)^2129*20000000000000^1617 ≤ 7027294710321^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259269859 5000000000 7027294710321 20000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(867651921/2000000000 : ℝ), (1041213169/2500000000 : ℝ), (2259269859/5000000000 : ℝ)] ![(33302487332143/100000000000000 : ℝ), (31561039104817/100000000000000 : ℝ), (7027294710321/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(867651921/2000000000 : ℝ)|^2129 ≤ (33302487332143/100000000000000 : ℝ)^1617
        have hw : |(867651921/2000000000 : ℝ)|=(867651921/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1041213169/2500000000 : ℝ)|^2129 ≤ (31561039104817/100000000000000 : ℝ)^1617
        have hw : |(1041213169/2500000000 : ℝ)|=(1041213169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2259269859/5000000000 : ℝ)|^2129 ≤ (7027294710321/20000000000000 : ℝ)^1617
        have hw : |(2259269859/5000000000 : ℝ)|=(2259269859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s7_4 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2082617053/10000000000 : ℝ)*x 0 + (209753103/400000000 : ℝ)*x 1 + (5414297051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2082617053/10000000000 : ℝ)^2129 ≤ (2534467939339/20000000000000 : ℝ)^1617 := by
    have hnat : (2082617053 : ℕ)^2129*20000000000000^1617 ≤ 2534467939339^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082617053 10000000000 2534467939339 20000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209753103/400000000 : ℝ)^2129 ≤ (21372192168163/50000000000000 : ℝ)^1617 := by
    have hnat : (209753103 : ℕ)^2129*50000000000000^1617 ≤ 21372192168163^1617*400000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209753103 400000000 21372192168163 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414297051/10000000000 : ℝ)^2129 ≤ (22291637976179/50000000000000 : ℝ)^1617 := by
    have hnat : (5414297051 : ℕ)^2129*50000000000000^1617 ≤ 22291637976179^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414297051 10000000000 22291637976179 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2082617053/10000000000 : ℝ), (209753103/400000000 : ℝ), (5414297051/10000000000 : ℝ)] ![(2534467939339/20000000000000 : ℝ), (21372192168163/50000000000000 : ℝ), (22291637976179/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2082617053/10000000000 : ℝ)|^2129 ≤ (2534467939339/20000000000000 : ℝ)^1617
        have hw : |(-2082617053/10000000000 : ℝ)|=(2082617053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209753103/400000000 : ℝ)|^2129 ≤ (21372192168163/50000000000000 : ℝ)^1617
        have hw : |(209753103/400000000 : ℝ)|=(209753103/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414297051/10000000000 : ℝ)|^2129 ≤ (22291637976179/50000000000000 : ℝ)^1617
        have hw : |(5414297051/10000000000 : ℝ)|=(5414297051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s7_5 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305701287/10000000000 : ℝ)*x 0 + (-1999039229/10000000000 : ℝ)*x 1 + (5414296959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305701287/10000000000 : ℝ)^2129 ≤ (21704837045923/50000000000000 : ℝ)^1617 := by
    have hnat : (5305701287 : ℕ)^2129*50000000000000^1617 ≤ 21704837045923^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305701287 10000000000 21704837045923 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1999039229/10000000000 : ℝ)^2129 ≤ (600352547319/5000000000000 : ℝ)^1617 := by
    have hnat : (1999039229 : ℕ)^2129*5000000000000^1617 ≤ 600352547319^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1999039229 10000000000 600352547319 5000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414296959/10000000000 : ℝ)^2129 ≤ (22291637477463/50000000000000 : ℝ)^1617 := by
    have hnat : (5414296959 : ℕ)^2129*50000000000000^1617 ≤ 22291637477463^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414296959 10000000000 22291637477463 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305701287/10000000000 : ℝ), (-1999039229/10000000000 : ℝ), (5414296959/10000000000 : ℝ)] ![(21704837045923/50000000000000 : ℝ), (600352547319/5000000000000 : ℝ), (22291637477463/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305701287/10000000000 : ℝ)|^2129 ≤ (21704837045923/50000000000000 : ℝ)^1617
        have hw : |(5305701287/10000000000 : ℝ)|=(5305701287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1999039229/10000000000 : ℝ)|^2129 ≤ (600352547319/5000000000000 : ℝ)^1617
        have hw : |(-1999039229/10000000000 : ℝ)|=(1999039229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414296959/10000000000 : ℝ)|^2129 ≤ (22291637477463/50000000000000 : ℝ)^1617
        have hw : |(5414296959/10000000000 : ℝ)|=(5414296959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s7_6 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305701081/10000000000 : ℝ)*x 0 + (2707148561/5000000000 : ℝ)*x 1 + (-399807857/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305701081/10000000000 : ℝ)^2129 ≤ (10852417968187/25000000000000 : ℝ)^1617 := by
    have hnat : (5305701081 : ℕ)^2129*25000000000000^1617 ≤ 10852417968187^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305701081 10000000000 10852417968187 25000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707148561/5000000000 : ℝ)^2129 ≤ (8916655344423/20000000000000 : ℝ)^1617 := by
    have hnat : (2707148561 : ℕ)^2129*20000000000000^1617 ≤ 8916655344423^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707148561 5000000000 8916655344423 20000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (399807857/2000000000 : ℝ)^2129 ≤ (12007051389243/100000000000000 : ℝ)^1617 := by
    have hnat : (399807857 : ℕ)^2129*100000000000000^1617 ≤ 12007051389243^1617*2000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399807857 2000000000 12007051389243 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305701081/10000000000 : ℝ), (2707148561/5000000000 : ℝ), (-399807857/2000000000 : ℝ)] ![(10852417968187/25000000000000 : ℝ), (8916655344423/20000000000000 : ℝ), (12007051389243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305701081/10000000000 : ℝ)|^2129 ≤ (10852417968187/25000000000000 : ℝ)^1617
        have hw : |(5305701081/10000000000 : ℝ)|=(5305701081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707148561/5000000000 : ℝ)|^2129 ≤ (8916655344423/20000000000000 : ℝ)^1617
        have hw : |(2707148561/5000000000 : ℝ)|=(2707148561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-399807857/2000000000 : ℝ)|^2129 ≤ (12007051389243/100000000000000 : ℝ)^1617
        have hw : |(-399807857/2000000000 : ℝ)|=(399807857/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s7_7 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (542285731/1250000000 : ℝ)*x 0 + (903455763/2000000000 : ℝ)*x 1 + (2083059921/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542285731/1250000000 : ℝ)^2129 ≤ (33302752573153/100000000000000 : ℝ)^1617 := by
    have hnat : (542285731 : ℕ)^2129*100000000000000^1617 ≤ 33302752573153^1617*1250000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542285731 1250000000 33302752573153 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (903455763/2000000000 : ℝ)^2129 ≤ (35123564682447/100000000000000 : ℝ)^1617 := by
    have hnat : (903455763 : ℕ)^2129*100000000000000^1617 ≤ 35123564682447^1617*2000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903455763 2000000000 35123564682447 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2083059921/5000000000 : ℝ)^2129 ≤ (3946710341641/12500000000000 : ℝ)^1617 := by
    have hnat : (2083059921 : ℕ)^2129*12500000000000^1617 ≤ 3946710341641^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083059921 5000000000 3946710341641 12500000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(542285731/1250000000 : ℝ), (903455763/2000000000 : ℝ), (2083059921/5000000000 : ℝ)] ![(33302752573153/100000000000000 : ℝ), (35123564682447/100000000000000 : ℝ), (3946710341641/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(542285731/1250000000 : ℝ)|^2129 ≤ (33302752573153/100000000000000 : ℝ)^1617
        have hw : |(542285731/1250000000 : ℝ)|=(542285731/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(903455763/2000000000 : ℝ)|^2129 ≤ (35123564682447/100000000000000 : ℝ)^1617
        have hw : |(903455763/2000000000 : ℝ)|=(903455763/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2083059921/5000000000 : ℝ)|^2129 ≤ (3946710341641/12500000000000 : ℝ)^1617
        have hw : |(2083059921/5000000000 : ℝ)|=(2083059921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1298_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76498753/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14679/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11041/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11043/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14677/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14679/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11041/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14679/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11041/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14679/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11041/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14679/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11041/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14679/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11041/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14679/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11041/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (11041/100000 : ℝ) ^ (4257/1024 : ℝ) ≤ (2101837504252403/20000000000000000000 : ℝ) := by
    have hpowers : (11041/100000 : ℝ)^4257 ≤ (2101837504252403/20000000000000000000 : ℝ)^1024 := by
      have hnat : (11041 : ℕ)^4257*20000000000000000000^1024 ≤ 2101837504252403^1024*100000^4257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11041 100000 2101837504252403 20000000000000000000 4257 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11041/100000 : ℝ)) (X := (2101837504252403/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14679/100000 : ℝ) ^ (4257/1024 : ℝ) ≤ (6867496205262573/20000000000000000000 : ℝ) := by
    have hpowers : (14679/100000 : ℝ)^4257 ≤ (6867496205262573/20000000000000000000 : ℝ)^1024 := by
      have hnat : (14679 : ℕ)^4257*20000000000000000000^1024 ≤ 6867496205262573^1024*100000^4257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14679 100000 6867496205262573 20000000000000000000 4257 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14679/100000 : ℝ)) (X := (6867496205262573/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002101837504252403/10000000000000000000 : ℝ) ≤ (2000101109224639/2000000000000000 : ℝ) ^ (4257/1024 : ℝ) := by
    have hpowers : (10002101837504252403/10000000000000000000 : ℝ)^1024 ≤ (2000101109224639/2000000000000000 : ℝ)^4257 := by
      have hnat : (10002101837504252403 : ℕ)^1024*2000000000000000^4257 ≤ 2000101109224639^4257*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002101837504252403 10000000000000000000 2000101109224639 2000000000000000 1024 4257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000101109224639/2000000000000000 : ℝ)) (X := (10002101837504252403/10000000000000000000 : ℝ)) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (625280291678422343/625000000000000000 : ℝ) ≤ (5000539290230061/5000000000000000 : ℝ) ^ (4257/1024 : ℝ) := by
    have hpowers : (625280291678422343/625000000000000000 : ℝ)^1024 ≤ (5000539290230061/5000000000000000 : ℝ)^4257 := by
      have hnat : (625280291678422343 : ℕ)^1024*5000000000000000^4257 ≤ 5000539290230061^4257*625000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625280291678422343 625000000000000000 5000539290230061 5000000000000000 1024 4257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000539290230061/5000000000000000 : ℝ)) (X := (625280291678422343/625000000000000000 : ℝ)) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006867496205262573/10000000000000000000 : ℝ) ≤ (10001651614797049/10000000000000000 : ℝ) ^ (4257/1024 : ℝ) := by
    have hpowers : (10006867496205262573/10000000000000000000 : ℝ)^1024 ≤ (10001651614797049/10000000000000000 : ℝ)^4257 := by
      have hnat : (10006867496205262573 : ℕ)^1024*10000000000000000^4257 ≤ 10001651614797049^4257*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006867496205262573 10000000000000000000 10001651614797049 10000000000000000 1024 4257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001651614797049/10000000000000000 : ℝ)) (X := (10006867496205262573/10000000000000000000 : ℝ)) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2101837504252403/20000000000000000000 : ℝ) ≤ ((9092296358142040349/9095000000000000000 : ℝ)+2*(573034336927/363800000000000 : ℝ)*(11041/100000 : ℝ))^(4257/1024 : ℝ) := by
    rw [show (9092296358142040349/9095000000000000000 : ℝ)+2*(573034336927/363800000000000 : ℝ)*(11041/100000 : ℝ)=(2000101109224639/2000000000000000 : ℝ) by norm_num, show 1+2*(2101837504252403/20000000000000000000 : ℝ)=(10002101837504252403/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6867496205262573/20000000000000000000 : ℝ)+(2101837504252403/20000000000000000000 : ℝ) ≤ ((9092296358142040349/9095000000000000000 : ℝ)+(573034336927/363800000000000 : ℝ)*((14679/100000 : ℝ)+(11041/100000 : ℝ)))^(4257/1024 : ℝ) := by
    rw [show (9092296358142040349/9095000000000000000 : ℝ)+(573034336927/363800000000000 : ℝ)*((14679/100000 : ℝ)+(11041/100000 : ℝ))=(5000539290230061/5000000000000000 : ℝ) by norm_num, show 1+(6867496205262573/20000000000000000000 : ℝ)+(2101837504252403/20000000000000000000 : ℝ)=(625280291678422343/625000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6867496205262573/20000000000000000000 : ℝ) ≤ ((9092296358142040349/9095000000000000000 : ℝ)+2*(573034336927/363800000000000 : ℝ)*(14679/100000 : ℝ))^(4257/1024 : ℝ) := by
    rw [show (9092296358142040349/9095000000000000000 : ℝ)+2*(573034336927/363800000000000 : ℝ)*(14679/100000 : ℝ)=(10001651614797049/10000000000000000 : ℝ) by norm_num, show 1+2*(6867496205262573/20000000000000000000 : ℝ)=(10006867496205262573/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9092296358142040349/9095000000000000000 : ℝ)*(X 1 0+X 2 0)+(573034336927/363800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4257/1024 : ℝ)) (lo := (11041/100000 : ℝ)) (hi := (14679/100000 : ℝ)) (c := (9092296358142040349/9095000000000000000 : ℝ)) (alpha := (573034336927/363800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9092296358142040349/9095000000000000000 : ℝ)*(X 0 1+X 2 1)+(573034336927/363800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4257/1024 : ℝ)) (lo := (11041/100000 : ℝ)) (hi := (14679/100000 : ℝ)) (c := (9092296358142040349/9095000000000000000 : ℝ)) (alpha := (573034336927/363800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9092296358142040349/9095000000000000000 : ℝ)*(X 0 2+X 1 2)+(573034336927/363800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4257/1024 : ℝ)) (lo := (11041/100000 : ℝ)) (hi := (14679/100000 : ℝ)) (c := (9092296358142040349/9095000000000000000 : ℝ)) (alpha := (573034336927/363800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-416520947/2000000000 : ℝ)*X 0 0+(5414912629/10000000000 : ℝ)*X 0 1+(2621607451/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674846213/5000000000 : ℝ)*X 1 0+(-2170120983/10000000000 : ℝ)*X 1 1+(5243216181/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674846381/5000000000 : ℝ)*X 2 0+(2621607499/5000000000 : ℝ)*X 2 1+(-2170122099/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((867651921/2000000000 : ℝ)*X 0 0+(1041213169/2500000000 : ℝ)*X 0 1+(2259269859/5000000000 : ℝ)*X 0 2+(867651921/2000000000 : ℝ)*X 1 0+(1041213169/2500000000 : ℝ)*X 1 1+(2259269859/5000000000 : ℝ)*X 1 2+(867651921/2000000000 : ℝ)*X 2 0+(1041213169/2500000000 : ℝ)*X 2 1+(2259269859/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2082617053/10000000000 : ℝ)*X 0 0+(209753103/400000000 : ℝ)*X 0 1+(5414297051/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305701287/10000000000 : ℝ)*X 1 0+(-1999039229/10000000000 : ℝ)*X 1 1+(5414296959/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305701081/10000000000 : ℝ)*X 2 0+(2707148561/5000000000 : ℝ)*X 2 1+(-399807857/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((542285731/1250000000 : ℝ)*X 0 0+(903455763/2000000000 : ℝ)*X 0 1+(2083059921/5000000000 : ℝ)*X 0 2+(542285731/1250000000 : ℝ)*X 1 0+(903455763/2000000000 : ℝ)*X 1 1+(2083059921/5000000000 : ℝ)*X 1 2+(542285731/1250000000 : ℝ)*X 2 0+(903455763/2000000000 : ℝ)*X 2 1+(2083059921/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (103323065621204243695168041/14210937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (12505677/10000000000000 : ℝ)*(base15) + (2546829/4000000000000 : ℝ)*(upper2) + (280727657/100000000000000 : ℝ)*(upper3) + (16203709/25000000000000 : ℝ)*(upper4) + (270363098057953/6250000000000 : ℝ)*(major0) + (270363098057953/6250000000000 : ℝ)*(major1) + (270363098057953/6250000000000 : ℝ)*(major2) + (145605574792943/2500000000000 : ℝ)*(sp0) + (5824246166781863/100000000000000 : ℝ)*(sp1) + (5824215287040047/100000000000000 : ℝ)*(sp2) + (2827363533256329/100000000000000 : ℝ)*(sp3) + (23300120913/100000000000000 : ℝ)*(sp4) + (6200959717/20000000000000 : ℝ)*(sp6) + (9070403791/100000000000000 : ℝ)*(sp7) + (70684315091503/2500000000000 : ℝ)*(f.failure) + (5824246291838633/100000000000000 : ℝ)*(f.sum) + (9060204979521/1136875000000000000000000000 : ℝ)*base65 + (458290196927754403/56843750000000000000000000000000 : ℝ)*base68 + (872593101819535653/56843750000000000000000000000000 : ℝ)*base70 + (703342098353160653/56843750000000000000000000000000 : ℝ)*base72 + (998272569213/2273750000000000000000000000 : ℝ)*base74 + (844065167750785653/56843750000000000000000000000000 : ℝ)*base76 + (139278924132495597/56843750000000000000000000000000 : ℝ)*base77 + (887888851015223153/56843750000000000000000000000000 : ℝ)*base80 + (2783135996089/4547500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (395759/125000000000000000000 : ℝ)*base89 + (395759/125000000000000000000 : ℝ)*base91 + (395759/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (545445714516742232200343937/56843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (872501787/50000000000000 : ℝ)*(base19) + (1807408051/100000000000000 : ℝ)*(base23) + (145948681/25000000000000 : ℝ)*(lower1) + (16244387/10000000000000 : ℝ)*(upper3) + (13370477/10000000000000 : ℝ)*(lower4) + (8229527/10000000000000 : ℝ)*(upper5) + (1089225931509371/25000000000000 : ℝ)*(major0) + (1089225931509371/25000000000000 : ℝ)*(major1) + (1089225931509371/25000000000000 : ℝ)*(major2) + (2301234563/50000000000000 : ℝ)*(sp2) + (5866111218777299/100000000000000 : ℝ)*(sp4) + (1466527368443431/25000000000000 : ℝ)*(sp5) + (2933052404450061/50000000000000 : ℝ)*(sp6) + (113907836537871/4000000000000 : ℝ)*(sp7) + (113907836537871/4000000000000 : ℝ)*(f.failure) + (5866111218777299/100000000000000 : ℝ)*(f.sum) + (53344179775299/9095000000000000000000000000 : ℝ)*base65 + (3344905423454714521/227375000000000000000000000000000 : ℝ)*base68 + (529789929696089521/227375000000000000000000000000000 : ℝ)*base70 + (1206930290830035479/227375000000000000000000000000000 : ℝ)*base71 + (30467086293921/9095000000000000000000000000 : ℝ)*base74 + (4692084862430214521/227375000000000000000000000000000 : ℝ)*base76 + (210415206396714521/227375000000000000000000000000000 : ℝ)*base78 + (1417897911708839521/227375000000000000000000000000000 : ℝ)*base80 + (8915327076941/2273750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (774863/200000000000000000000 : ℝ)*base89 + (774863/200000000000000000000 : ℝ)*base91 + (774863/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1298_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76498753/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14679/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11041/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11043/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14677/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1298_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1298_s8_0 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1337422193/2500000000 : ℝ)*x 0 + (2621615923/5000000000 : ℝ)*x 1 + (-2170105131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337422193/2500000000 : ℝ)^2129 ≤ (10971035567919/25000000000000 : ℝ)^1617 := by
    have hnat : (1337422193 : ℕ)^2129*25000000000000^1617 ≤ 10971035567919^1617*2500000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337422193 2500000000 10971035567919 25000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621615923/5000000000 : ℝ)^2129 ≤ (267112442859/625000000000 : ℝ)^1617 := by
    have hnat : (2621615923 : ℕ)^2129*625000000000^1617 ≤ 267112442859^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621615923 5000000000 267112442859 625000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2170105131/10000000000 : ℝ)^2129 ≤ (3344466712949/25000000000000 : ℝ)^1617 := by
    have hnat : (2170105131 : ℕ)^2129*25000000000000^1617 ≤ 3344466712949^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170105131 10000000000 3344466712949 25000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337422193/2500000000 : ℝ), (2621615923/5000000000 : ℝ), (-2170105131/10000000000 : ℝ)] ![(10971035567919/25000000000000 : ℝ), (267112442859/625000000000 : ℝ), (3344466712949/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337422193/2500000000 : ℝ)|^2129 ≤ (10971035567919/25000000000000 : ℝ)^1617
        have hw : |(1337422193/2500000000 : ℝ)|=(1337422193/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621615923/5000000000 : ℝ)|^2129 ≤ (267112442859/625000000000 : ℝ)^1617
        have hw : |(2621615923/5000000000 : ℝ)|=(2621615923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2170105131/10000000000 : ℝ)|^2129 ≤ (3344466712949/25000000000000 : ℝ)^1617
        have hw : |(-2170105131/10000000000 : ℝ)|=(2170105131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s8_1 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2082618957/10000000000 : ℝ)*x 0 + (5243843721/10000000000 : ℝ)*x 1 + (5414279661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2082618957/10000000000 : ℝ)^2129 ≤ (2534470990113/20000000000000 : ℝ)^1617 := by
    have hnat : (2082618957 : ℕ)^2129*20000000000000^1617 ≤ 2534470990113^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082618957 10000000000 2534470990113 20000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243843721/10000000000 : ℝ)^2129 ≤ (42744557621523/100000000000000 : ℝ)^1617 := by
    have hnat : (5243843721 : ℕ)^2129*100000000000000^1617 ≤ 42744557621523^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243843721 10000000000 42744557621523 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414279661/10000000000 : ℝ)^2129 ≤ (44583087416093/100000000000000 : ℝ)^1617 := by
    have hnat : (5414279661 : ℕ)^2129*100000000000000^1617 ≤ 44583087416093^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414279661 10000000000 44583087416093 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2082618957/10000000000 : ℝ), (5243843721/10000000000 : ℝ), (5414279661/10000000000 : ℝ)] ![(2534470990113/20000000000000 : ℝ), (42744557621523/100000000000000 : ℝ), (44583087416093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2082618957/10000000000 : ℝ)|^2129 ≤ (2534470990113/20000000000000 : ℝ)^1617
        have hw : |(-2082618957/10000000000 : ℝ)|=(2082618957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243843721/10000000000 : ℝ)|^2129 ≤ (42744557621523/100000000000000 : ℝ)^1617
        have hw : |(5243843721/10000000000 : ℝ)|=(5243843721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414279661/10000000000 : ℝ)|^2129 ≤ (44583087416093/100000000000000 : ℝ)^1617
        have hw : |(5414279661/10000000000 : ℝ)|=(5414279661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s8_2 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (530570543/1000000000 : ℝ)*x 0 + (-999528651/5000000000 : ℝ)*x 1 + (5414279659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530570543/1000000000 : ℝ)^2129 ≤ (21704859360793/50000000000000 : ℝ)^1617 := by
    have hnat : (530570543 : ℕ)^2129*50000000000000^1617 ≤ 21704859360793^1617*1000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530570543 1000000000 21704859360793 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (999528651/5000000000 : ℝ)^2129 ≤ (6003596936241/50000000000000 : ℝ)^1617 := by
    have hnat : (999528651 : ℕ)^2129*50000000000000^1617 ≤ 6003596936241^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999528651 5000000000 6003596936241 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414279659/10000000000 : ℝ)^2129 ≤ (44583087394409/100000000000000 : ℝ)^1617 := by
    have hnat : (5414279659 : ℕ)^2129*100000000000000^1617 ≤ 44583087394409^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414279659 10000000000 44583087394409 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530570543/1000000000 : ℝ), (-999528651/5000000000 : ℝ), (5414279659/10000000000 : ℝ)] ![(21704859360793/50000000000000 : ℝ), (6003596936241/50000000000000 : ℝ), (44583087394409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530570543/1000000000 : ℝ)|^2129 ≤ (21704859360793/50000000000000 : ℝ)^1617
        have hw : |(530570543/1000000000 : ℝ)|=(530570543/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-999528651/5000000000 : ℝ)|^2129 ≤ (6003596936241/50000000000000 : ℝ)^1617
        have hw : |(-999528651/5000000000 : ℝ)|=(999528651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414279659/10000000000 : ℝ)|^2129 ≤ (44583087394409/100000000000000 : ℝ)^1617
        have hw : |(5414279659/10000000000 : ℝ)|=(5414279659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s8_3 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (530570543/1000000000 : ℝ)*x 0 + (2707139829/5000000000 : ℝ)*x 1 + (-1999057303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530570543/1000000000 : ℝ)^2129 ≤ (21704859360793/50000000000000 : ℝ)^1617 := by
    have hnat : (530570543 : ℕ)^2129*50000000000000^1617 ≤ 21704859360793^1617*1000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530570543 1000000000 21704859360793 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707139829/5000000000 : ℝ)^2129 ≤ (2786442961473/6250000000000 : ℝ)^1617 := by
    have hnat : (2707139829 : ℕ)^2129*6250000000000^1617 ≤ 2786442961473^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707139829 5000000000 2786442961473 6250000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1999057303/10000000000 : ℝ)^2129 ≤ (1200719388039/10000000000000 : ℝ)^1617 := by
    have hnat : (1999057303 : ℕ)^2129*10000000000000^1617 ≤ 1200719388039^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1999057303 10000000000 1200719388039 10000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530570543/1000000000 : ℝ), (2707139829/5000000000 : ℝ), (-1999057303/10000000000 : ℝ)] ![(21704859360793/50000000000000 : ℝ), (2786442961473/6250000000000 : ℝ), (1200719388039/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530570543/1000000000 : ℝ)|^2129 ≤ (21704859360793/50000000000000 : ℝ)^1617
        have hw : |(530570543/1000000000 : ℝ)|=(530570543/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707139829/5000000000 : ℝ)|^2129 ≤ (2786442961473/6250000000000 : ℝ)^1617
        have hw : |(2707139829/5000000000 : ℝ)|=(2707139829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1999057303/10000000000 : ℝ)|^2129 ≤ (1200719388039/10000000000000 : ℝ)^1617
        have hw : |(-1999057303/10000000000 : ℝ)|=(1999057303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s8_4 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (216914359/500000000 : ℝ)*x 0 + (36137951/80000000 : ℝ)*x 1 + (4166154339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216914359/500000000 : ℝ)^2129 ≤ (33302766035843/100000000000000 : ℝ)^1617 := by
    have hnat : (216914359 : ℕ)^2129*100000000000000^1617 ≤ 33302766035843^1617*500000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216914359 500000000 33302766035843 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (36137951/80000000 : ℝ)^2129 ≤ (17561603495029/50000000000000 : ℝ)^1617 := by
    have hnat : (36137951 : ℕ)^2129*50000000000000^1617 ≤ 17561603495029^1617*80000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36137951 80000000 17561603495029 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4166154339/10000000000 : ℝ)^2129 ≤ (7893506739257/25000000000000 : ℝ)^1617 := by
    have hnat : (4166154339 : ℕ)^2129*25000000000000^1617 ≤ 7893506739257^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4166154339 10000000000 7893506739257 25000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(216914359/500000000 : ℝ), (36137951/80000000 : ℝ), (4166154339/10000000000 : ℝ)] ![(33302766035843/100000000000000 : ℝ), (17561603495029/50000000000000 : ℝ), (7893506739257/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(216914359/500000000 : ℝ)|^2129 ≤ (33302766035843/100000000000000 : ℝ)^1617
        have hw : |(216914359/500000000 : ℝ)|=(216914359/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(36137951/80000000 : ℝ)|^2129 ≤ (17561603495029/50000000000000 : ℝ)^1617
        have hw : |(36137951/80000000 : ℝ)|=(36137951/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4166154339/10000000000 : ℝ)|^2129 ≤ (7893506739257/25000000000000 : ℝ)^1617
        have hw : |(4166154339/10000000000 : ℝ)|=(4166154339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1298_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76498753/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14677/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11043/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11043/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3669/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14677/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11043/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14677/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11043/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14677/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11043/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14677/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11043/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14677/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11043/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14677/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11043/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11043/100000 : ℝ) ^ (4257/1024 : ℝ) ≤ (10517103754979943/100000000000000000000 : ℝ) := by
    have hpowers : (11043/100000 : ℝ)^4257 ≤ (10517103754979943/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11043 : ℕ)^4257*100000000000000000000^1024 ≤ 10517103754979943^1024*100000^4257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11043 100000 10517103754979943 100000000000000000000 4257 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11043/100000 : ℝ)) (X := (10517103754979943/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14677/100000 : ℝ) ^ (4257/1024 : ℝ) ≤ (34318035834109293/100000000000000000000 : ℝ) := by
    have hpowers : (14677/100000 : ℝ)^4257 ≤ (34318035834109293/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14677 : ℕ)^4257*100000000000000000000^1024 ≤ 34318035834109293^1024*100000^4257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14677 100000 34318035834109293 100000000000000000000 4257 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14677/100000 : ℝ)) (X := (34318035834109293/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010517103754979943/50000000000000000000 : ℝ) ≤ (2000101185380891/2000000000000000 : ℝ) ^ (4257/1024 : ℝ) := by
    have hpowers : (50010517103754979943/50000000000000000000 : ℝ)^1024 ≤ (2000101185380891/2000000000000000 : ℝ)^4257 := by
      have hnat : (50010517103754979943 : ℕ)^1024*2000000000000000^4257 ≤ 2000101185380891^4257*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010517103754979943 50000000000000000000 2000101185380891 2000000000000000 1024 4257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000101185380891/2000000000000000 : ℝ)) (X := (50010517103754979943/50000000000000000000 : ℝ)) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011208784897272309/25000000000000000000 : ℝ) ≤ (2500269575807803/2500000000000000 : ℝ) ^ (4257/1024 : ℝ) := by
    have hpowers : (25011208784897272309/25000000000000000000 : ℝ)^1024 ≤ (2500269575807803/2500000000000000 : ℝ)^4257 := by
      have hnat : (25011208784897272309 : ℕ)^1024*2500000000000000^4257 ≤ 2500269575807803^4257*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011208784897272309 25000000000000000000 2500269575807803 2500000000000000 1024 4257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500269575807803/2500000000000000 : ℝ)) (X := (25011208784897272309/25000000000000000000 : ℝ)) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034318035834109293/50000000000000000000 : ℝ) ≤ (10001650679557969/10000000000000000 : ℝ) ^ (4257/1024 : ℝ) := by
    have hpowers : (50034318035834109293/50000000000000000000 : ℝ)^1024 ≤ (10001650679557969/10000000000000000 : ℝ)^4257 := by
      have hnat : (50034318035834109293 : ℕ)^1024*10000000000000000^4257 ≤ 10001650679557969^4257*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034318035834109293 50000000000000000000 10001650679557969 10000000000000000 1024 4257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001650679557969/10000000000000000 : ℝ)) (X := (50034318035834109293/50000000000000000000 : ℝ)) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10517103754979943/100000000000000000000 : ℝ) ≤ ((567643703669031787/567812500000000000 : ℝ)+2*(572376326757/363400000000000 : ℝ)*(11043/100000 : ℝ))^(4257/1024 : ℝ) := by
    rw [show (567643703669031787/567812500000000000 : ℝ)+2*(572376326757/363400000000000 : ℝ)*(11043/100000 : ℝ)=(2000101185380891/2000000000000000 : ℝ) by norm_num, show 1+2*(10517103754979943/100000000000000000000 : ℝ)=(50010517103754979943/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34318035834109293/100000000000000000000 : ℝ)+(10517103754979943/100000000000000000000 : ℝ) ≤ ((567643703669031787/567812500000000000 : ℝ)+(572376326757/363400000000000 : ℝ)*((14677/100000 : ℝ)+(11043/100000 : ℝ)))^(4257/1024 : ℝ) := by
    rw [show (567643703669031787/567812500000000000 : ℝ)+(572376326757/363400000000000 : ℝ)*((14677/100000 : ℝ)+(11043/100000 : ℝ))=(2500269575807803/2500000000000000 : ℝ) by norm_num, show 1+(34318035834109293/100000000000000000000 : ℝ)+(10517103754979943/100000000000000000000 : ℝ)=(25011208784897272309/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34318035834109293/100000000000000000000 : ℝ) ≤ ((567643703669031787/567812500000000000 : ℝ)+2*(572376326757/363400000000000 : ℝ)*(14677/100000 : ℝ))^(4257/1024 : ℝ) := by
    rw [show (567643703669031787/567812500000000000 : ℝ)+2*(572376326757/363400000000000 : ℝ)*(14677/100000 : ℝ)=(10001650679557969/10000000000000000 : ℝ) by norm_num, show 1+2*(34318035834109293/100000000000000000000 : ℝ)=(50034318035834109293/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (567643703669031787/567812500000000000 : ℝ)*(X 1 0+X 2 0)+(572376326757/363400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4257/1024 : ℝ)) (lo := (11043/100000 : ℝ)) (hi := (14677/100000 : ℝ)) (c := (567643703669031787/567812500000000000 : ℝ)) (alpha := (572376326757/363400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (567643703669031787/567812500000000000 : ℝ)*(X 0 1+X 2 1)+(572376326757/363400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4257/1024 : ℝ)) (lo := (11043/100000 : ℝ)) (hi := (14677/100000 : ℝ)) (c := (567643703669031787/567812500000000000 : ℝ)) (alpha := (572376326757/363400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (567643703669031787/567812500000000000 : ℝ)*(X 0 2+X 1 2)+(572376326757/363400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4257/1024 : ℝ)) (lo := (11043/100000 : ℝ)) (hi := (14677/100000 : ℝ)) (c := (567643703669031787/567812500000000000 : ℝ)) (alpha := (572376326757/363400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((1337422193/2500000000 : ℝ)*X 2 0+(2621615923/5000000000 : ℝ)*X 2 1+(-2170105131/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s8_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-2082618957/10000000000 : ℝ)*X 0 0+(5243843721/10000000000 : ℝ)*X 0 1+(5414279661/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s8_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((530570543/1000000000 : ℝ)*X 1 0+(-999528651/5000000000 : ℝ)*X 1 1+(5414279659/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s8_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((530570543/1000000000 : ℝ)*X 2 0+(2707139829/5000000000 : ℝ)*X 2 1+(-1999057303/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s8_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((216914359/500000000 : ℝ)*X 0 0+(36137951/80000000 : ℝ)*X 0 1+(4166154339/10000000000 : ℝ)*X 0 2+(216914359/500000000 : ℝ)*X 1 0+(36137951/80000000 : ℝ)*X 1 1+(4166154339/10000000000 : ℝ)*X 1 2+(216914359/500000000 : ℝ)*X 2 0+(36137951/80000000 : ℝ)*X 2 1+(4166154339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s8_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (31320398452385769772521/9085000000000000000000000000 : ℝ) := by norm_num
    linear_combination (610081251/100000000000000 : ℝ)*(base19) + (66221383/10000000000000 : ℝ)*(base23) + (52268977/25000000000000 : ℝ)*(lower1) + (69516833/100000000000000 : ℝ)*(upper3) + (1188643/5000000000000 : ℝ)*(lower4) + (8732941/12500000000000 : ℝ)*(upper5) + (1089445581677721/25000000000000 : ℝ)*(major0) + (1089445581677721/25000000000000 : ℝ)*(major1) + (1089445581677721/25000000000000 : ℝ)*(major2) + (883777329/100000000000000 : ℝ)*(sp0) + (45838237241343/781250000000 : ℝ)*(sp1) + (5867293756810653/100000000000000 : ℝ)*(sp2) + (1173458564180149/20000000000000 : ℝ)*(sp3) + (1424135085806851/50000000000000 : ℝ)*(sp4) + (1424135085806851/50000000000000 : ℝ)*(f.failure) + (45838237241343/781250000000 : ℝ)*(f.sum) + (24758355403063/4542500000000000000000000000 : ℝ)*base66 + (209032194783394229/28390625000000000000000000000000 : ℝ)*base67 + (22315358756894229/28390625000000000000000000000000 : ℝ)*base69 + (645516422447418271/28390625000000000000000000000000 : ℝ)*base72 + (3207921441573/4542500000000000000000000000 : ℝ)*base74 + (40508187314607573/14195312500000000000000000000000 : ℝ)*base76 + (120092155228894229/28390625000000000000000000000000 : ℝ)*base77 + (245218650121605771/28390625000000000000000000000000 : ℝ)*base80 + (9793865520823/4542500000000000000000000000 : ℝ)*base82 + (356803/2500000000000000000000 : ℝ)*base89 + (356803/2500000000000000000000 : ℝ)*base91 + (356803/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1298_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76498753/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14677/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11043/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11043/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3669/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1298_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1298_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76498753/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1469/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1103/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11043/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3669/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1298_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1298_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1298_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76498753/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1469/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1103/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11043/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3669/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1298_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

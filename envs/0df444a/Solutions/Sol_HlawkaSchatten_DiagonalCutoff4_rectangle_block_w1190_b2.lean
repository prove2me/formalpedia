-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1190_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:53:09.084148+00:00
-- url     : https://prove2.me/submissions/ed635c98-d1ec-45ea-bd89-46ff41825506

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
theorem support_rectangle_w1190_s6_0 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-428823053/2000000000 : ℝ)*x 0 + (5392424551/10000000000 : ℝ)*x 1 + (526623441/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (428823053/2000000000 : ℝ)^8383 ≤ (6516610895853/50000000000000 : ℝ)^6335 := by
    have hnat : (428823053 : ℕ)^8383*50000000000000^6335 ≤ 6516610895853^6335*2000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428823053 2000000000 6516610895853 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392424551/10000000000 : ℝ)^8383 ≤ (44164603546347/100000000000000 : ℝ)^6335 := by
    have hnat : (5392424551 : ℕ)^8383*100000000000000^6335 ≤ 44164603546347^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392424551 10000000000 44164603546347 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526623441/1000000000 : ℝ)^8383 ≤ (42802174647649/100000000000000 : ℝ)^6335 := by
    have hnat : (526623441 : ℕ)^8383*100000000000000^6335 ≤ 42802174647649^6335*1000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526623441 1000000000 42802174647649 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-428823053/2000000000 : ℝ), (5392424551/10000000000 : ℝ), (526623441/1000000000 : ℝ)] ![(6516610895853/50000000000000 : ℝ), (44164603546347/100000000000000 : ℝ), (42802174647649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-428823053/2000000000 : ℝ)|^8383 ≤ (6516610895853/50000000000000 : ℝ)^6335
        have hw : |(-428823053/2000000000 : ℝ)|=(428823053/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392424551/10000000000 : ℝ)|^8383 ≤ (44164603546347/100000000000000 : ℝ)^6335
        have hw : |(5392424551/10000000000 : ℝ)|=(5392424551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526623441/1000000000 : ℝ)|^8383 ≤ (42802174647649/100000000000000 : ℝ)^6335
        have hw : |(526623441/1000000000 : ℝ)|=(526623441/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s6_1 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344629929/10000000000 : ℝ)*x 0 + (-17250883/78125000 : ℝ)*x 1 + (5266234469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344629929/10000000000 : ℝ)^8383 ≤ (21823678120529/50000000000000 : ℝ)^6335 := by
    have hnat : (5344629929 : ℕ)^8383*50000000000000^6335 ≤ 21823678120529^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344629929 10000000000 21823678120529 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17250883/78125000 : ℝ)^8383 ≤ (6775234231127/50000000000000 : ℝ)^6335 := by
    have hnat : (17250883 : ℕ)^8383*50000000000000^6335 ≤ 6775234231127^6335*78125000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17250883 78125000 6775234231127 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266234469/10000000000 : ℝ)^8383 ≤ (21401087641103/50000000000000 : ℝ)^6335 := by
    have hnat : (5266234469 : ℕ)^8383*50000000000000^6335 ≤ 21401087641103^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266234469 10000000000 21401087641103 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344629929/10000000000 : ℝ), (-17250883/78125000 : ℝ), (5266234469/10000000000 : ℝ)] ![(21823678120529/50000000000000 : ℝ), (6775234231127/50000000000000 : ℝ), (21401087641103/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344629929/10000000000 : ℝ)|^8383 ≤ (21823678120529/50000000000000 : ℝ)^6335
        have hw : |(5344629929/10000000000 : ℝ)|=(5344629929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-17250883/78125000 : ℝ)|^8383 ≤ (6775234231127/50000000000000 : ℝ)^6335
        have hw : |(-17250883/78125000 : ℝ)|=(17250883/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266234469/10000000000 : ℝ)|^8383 ≤ (21401087641103/50000000000000 : ℝ)^6335
        have hw : |(5266234469/10000000000 : ℝ)|=(5266234469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s6_2 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336157509/2500000000 : ℝ)*x 0 + (164569821/312500000 : ℝ)*x 1 + (-2208113143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336157509/2500000000 : ℝ)^8383 ≤ (349178859179/800000000000 : ℝ)^6335 := by
    have hnat : (1336157509 : ℕ)^8383*800000000000^6335 ≤ 349178859179^6335*2500000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336157509 2500000000 349178859179 800000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164569821/312500000 : ℝ)^8383 ≤ (42802173163431/100000000000000 : ℝ)^6335 := by
    have hnat : (164569821 : ℕ)^8383*100000000000000^6335 ≤ 42802173163431^6335*312500000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164569821 312500000 42802173163431 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2208113143/10000000000 : ℝ)^8383 ≤ (67752347143/500000000000 : ℝ)^6335 := by
    have hnat : (2208113143 : ℕ)^8383*500000000000^6335 ≤ 67752347143^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2208113143 10000000000 67752347143 500000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336157509/2500000000 : ℝ), (164569821/312500000 : ℝ), (-2208113143/10000000000 : ℝ)] ![(349178859179/800000000000 : ℝ), (42802173163431/100000000000000 : ℝ), (67752347143/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336157509/2500000000 : ℝ)|^8383 ≤ (349178859179/800000000000 : ℝ)^6335
        have hw : |(1336157509/2500000000 : ℝ)|=(1336157509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164569821/312500000 : ℝ)|^8383 ≤ (42802173163431/100000000000000 : ℝ)^6335
        have hw : |(164569821/312500000 : ℝ)|=(164569821/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2208113143/10000000000 : ℝ)|^8383 ≤ (67752347143/500000000000 : ℝ)^6335
        have hw : |(-2208113143/10000000000 : ℝ)|=(2208113143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s6_3 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4357941767/10000000000 : ℝ)*x 0 + (4233044847/10000000000 : ℝ)*x 1 + (179458531/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357941767/10000000000 : ℝ)^8383 ≤ (33317093979743/100000000000000 : ℝ)^6335 := by
    have hnat : (4357941767 : ℕ)^8383*100000000000000^6335 ≤ 33317093979743^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357941767 10000000000 33317093979743 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4233044847/10000000000 : ℝ)^8383 ≤ (32059442059779/100000000000000 : ℝ)^6335 := by
    have hnat : (4233044847 : ℕ)^8383*100000000000000^6335 ≤ 32059442059779^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233044847 10000000000 32059442059779 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (179458531/400000000 : ℝ)^8383 ≤ (34623463940259/100000000000000 : ℝ)^6335 := by
    have hnat : (179458531 : ℕ)^8383*100000000000000^6335 ≤ 34623463940259^6335*400000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179458531 400000000 34623463940259 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357941767/10000000000 : ℝ), (4233044847/10000000000 : ℝ), (179458531/400000000 : ℝ)] ![(33317093979743/100000000000000 : ℝ), (32059442059779/100000000000000 : ℝ), (34623463940259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357941767/10000000000 : ℝ)|^8383 ≤ (33317093979743/100000000000000 : ℝ)^6335
        have hw : |(4357941767/10000000000 : ℝ)|=(4357941767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4233044847/10000000000 : ℝ)|^8383 ≤ (32059442059779/100000000000000 : ℝ)^6335
        have hw : |(4233044847/10000000000 : ℝ)|=(4233044847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(179458531/400000000 : ℝ)|^8383 ≤ (34623463940259/100000000000000 : ℝ)^6335
        have hw : |(179458531/400000000 : ℝ)|=(179458531/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s6_4 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2144120229/10000000000 : ℝ)*x 0 + (263327659/500000000 : ℝ)*x 1 + (5392104521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2144120229/10000000000 : ℝ)^8383 ≤ (13033261720707/100000000000000 : ℝ)^6335 := by
    have hnat : (2144120229 : ℕ)^8383*100000000000000^6335 ≤ 13033261720707^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144120229 10000000000 13033261720707 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263327659/500000000 : ℝ)^8383 ≤ (10701400779083/25000000000000 : ℝ)^6335 := by
    have hnat : (263327659 : ℕ)^8383*25000000000000^6335 ≤ 10701400779083^6335*500000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263327659 500000000 10701400779083 25000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392104521/10000000000 : ℝ)^8383 ≤ (1766445405709/4000000000000 : ℝ)^6335 := by
    have hnat : (5392104521 : ℕ)^8383*4000000000000^6335 ≤ 1766445405709^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392104521 10000000000 1766445405709 4000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2144120229/10000000000 : ℝ), (263327659/500000000 : ℝ), (5392104521/10000000000 : ℝ)] ![(13033261720707/100000000000000 : ℝ), (10701400779083/25000000000000 : ℝ), (1766445405709/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2144120229/10000000000 : ℝ)|^8383 ≤ (13033261720707/100000000000000 : ℝ)^6335
        have hw : |(-2144120229/10000000000 : ℝ)|=(2144120229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263327659/500000000 : ℝ)|^8383 ≤ (10701400779083/25000000000000 : ℝ)^6335
        have hw : |(263327659/500000000 : ℝ)|=(263327659/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392104521/10000000000 : ℝ)|^8383 ≤ (1766445405709/4000000000000 : ℝ)^6335
        have hw : |(5392104521/10000000000 : ℝ)|=(5392104521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s6_5 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312547757/10000000000 : ℝ)*x 0 + (-83289711/400000000 : ℝ)*x 1 + (1078420907/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312547757/10000000000 : ℝ)^8383 ≤ (21650495322783/50000000000000 : ℝ)^6335 := by
    have hnat : (5312547757 : ℕ)^8383*50000000000000^6335 ≤ 21650495322783^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312547757 10000000000 21650495322783 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (83289711/400000000 : ℝ)^8383 ≤ (3918085639/31250000000 : ℝ)^6335 := by
    have hnat : (83289711 : ℕ)^8383*31250000000^6335 ≤ 3918085639^6335*400000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83289711 400000000 3918085639 31250000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078420907/2000000000 : ℝ)^8383 ≤ (11040283823613/25000000000000 : ℝ)^6335 := by
    have hnat : (1078420907 : ℕ)^8383*25000000000000^6335 ≤ 11040283823613^6335*2000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078420907 2000000000 11040283823613 25000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312547757/10000000000 : ℝ), (-83289711/400000000 : ℝ), (1078420907/2000000000 : ℝ)] ![(21650495322783/50000000000000 : ℝ), (3918085639/31250000000 : ℝ), (11040283823613/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312547757/10000000000 : ℝ)|^8383 ≤ (21650495322783/50000000000000 : ℝ)^6335
        have hw : |(5312547757/10000000000 : ℝ)|=(5312547757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-83289711/400000000 : ℝ)|^8383 ≤ (3918085639/31250000000 : ℝ)^6335
        have hw : |(-83289711/400000000 : ℝ)|=(83289711/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078420907/2000000000 : ℝ)|^8383 ≤ (11040283823613/25000000000000 : ℝ)^6335
        have hw : |(1078420907/2000000000 : ℝ)|=(1078420907/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s6_6 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062509553/2000000000 : ℝ)*x 0 + (5392104533/10000000000 : ℝ)*x 1 + (-2082242767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062509553/2000000000 : ℝ)^8383 ≤ (43300990731851/100000000000000 : ℝ)^6335 := by
    have hnat : (1062509553 : ℕ)^8383*100000000000000^6335 ≤ 43300990731851^6335*2000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062509553 2000000000 43300990731851 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392104533/10000000000 : ℝ)^8383 ≤ (44161135272777/100000000000000 : ℝ)^6335 := by
    have hnat : (5392104533 : ℕ)^8383*100000000000000^6335 ≤ 44161135272777^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392104533 10000000000 44161135272777 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2082242767/10000000000 : ℝ)^8383 ≤ (12537873981057/100000000000000 : ℝ)^6335 := by
    have hnat : (2082242767 : ℕ)^8383*100000000000000^6335 ≤ 12537873981057^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082242767 10000000000 12537873981057 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062509553/2000000000 : ℝ), (5392104533/10000000000 : ℝ), (-2082242767/10000000000 : ℝ)] ![(43300990731851/100000000000000 : ℝ), (44161135272777/100000000000000 : ℝ), (12537873981057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062509553/2000000000 : ℝ)|^8383 ≤ (43300990731851/100000000000000 : ℝ)^6335
        have hw : |(1062509553/2000000000 : ℝ)|=(1062509553/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392104533/10000000000 : ℝ)|^8383 ≤ (44161135272777/100000000000000 : ℝ)^6335
        have hw : |(5392104533/10000000000 : ℝ)|=(5392104533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2082242767/10000000000 : ℝ)|^8383 ≤ (12537873981057/100000000000000 : ℝ)^6335
        have hw : |(-2082242767/10000000000 : ℝ)|=(2082242767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s6_7 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4357951333/10000000000 : ℝ)*x 0 + (11214557/25000000 : ℝ)*x 1 + (1058421947/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357951333/10000000000 : ℝ)^8383 ≤ (4164648844507/12500000000000 : ℝ)^6335 := by
    have hnat : (4357951333 : ℕ)^8383*12500000000000^6335 ≤ 4164648844507^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357951333 10000000000 4164648844507 12500000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (11214557/25000000 : ℝ)^8383 ≤ (34616923433401/100000000000000 : ℝ)^6335 := by
    have hnat : (11214557 : ℕ)^8383*100000000000000^6335 ≤ 34616923433401^6335*25000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11214557 25000000 34616923433401 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1058421947/2500000000 : ℝ)^8383 ≤ (2004117862219/6250000000000 : ℝ)^6335 := by
    have hnat : (1058421947 : ℕ)^8383*6250000000000^6335 ≤ 2004117862219^6335*2500000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058421947 2500000000 2004117862219 6250000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357951333/10000000000 : ℝ), (11214557/25000000 : ℝ), (1058421947/2500000000 : ℝ)] ![(4164648844507/12500000000000 : ℝ), (34616923433401/100000000000000 : ℝ), (2004117862219/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357951333/10000000000 : ℝ)|^8383 ≤ (4164648844507/12500000000000 : ℝ)^6335
        have hw : |(4357951333/10000000000 : ℝ)|=(4357951333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(11214557/25000000 : ℝ)|^8383 ≤ (34616923433401/100000000000000 : ℝ)^6335
        have hw : |(11214557/25000000 : ℝ)|=(11214557/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1058421947/2500000000 : ℝ)|^8383 ≤ (2004117862219/6250000000000 : ℝ)^6335
        have hw : |(1058421947/2500000000 : ℝ)|=(1058421947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1190_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30082221/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14109/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1423/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11409/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7041/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14109/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1423/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14109/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1423/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14109/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1423/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14109/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1423/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14109/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1423/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14109/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1423/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1423/12500 : ℝ) ^ (4191/1024 : ℝ) ≤ (3432169990239857/25000000000000000000 : ℝ) := by
    have hpowers : (1423/12500 : ℝ)^4191 ≤ (3432169990239857/25000000000000000000 : ℝ)^1024 := by
      have hnat : (1423 : ℕ)^4191*25000000000000000000^1024 ≤ 3432169990239857^1024*12500^4191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1423 12500 3432169990239857 25000000000000000000 4191 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1423/12500 : ℝ)) (X := (3432169990239857/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14109/100000 : ℝ) ^ (4191/1024 : ℝ) ≤ (165215496625301/500000000000000000 : ℝ) := by
    have hpowers : (14109/100000 : ℝ)^4191 ≤ (165215496625301/500000000000000000 : ℝ)^1024 := by
      have hnat : (14109 : ℕ)^4191*500000000000000000^1024 ≤ 165215496625301^1024*100000^4191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14109 100000 165215496625301 500000000000000000 4191 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14109/100000 : ℝ)) (X := (165215496625301/500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503432169990239857/12500000000000000000 : ℝ) ≤ (10000670804584897/10000000000000000 : ℝ) ^ (4191/1024 : ℝ) := by
    have hpowers : (12503432169990239857/12500000000000000000 : ℝ)^1024 ≤ (10000670804584897/10000000000000000 : ℝ)^4191 := by
      have hnat : (12503432169990239857 : ℕ)^1024*10000000000000000^4191 ≤ 10000670804584897^4191*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503432169990239857 12500000000000000000 10000670804584897 10000000000000000 1024 4191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000670804584897/10000000000000000 : ℝ)) (X := (12503432169990239857/12500000000000000000 : ℝ)) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011692944821504907/25000000000000000000 : ℝ) ≤ (5000571293730031/5000000000000000 : ℝ) ^ (4191/1024 : ℝ) := by
    have hpowers : (25011692944821504907/25000000000000000000 : ℝ)^1024 ≤ (5000571293730031/5000000000000000 : ℝ)^4191 := by
      have hnat : (25011692944821504907 : ℕ)^1024*5000000000000000^4191 ≤ 5000571293730031^4191*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011692944821504907 25000000000000000000 5000571293730031 5000000000000000 1024 4191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000571293730031/5000000000000000 : ℝ)) (X := (25011692944821504907/25000000000000000000 : ℝ)) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (250165215496625301/250000000000000000 : ℝ) ≤ (10001614370335227/10000000000000000 : ℝ) ^ (4191/1024 : ℝ) := by
    have hpowers : (250165215496625301/250000000000000000 : ℝ)^1024 ≤ (10001614370335227/10000000000000000 : ℝ)^4191 := by
      have hnat : (250165215496625301 : ℕ)^1024*10000000000000000^4191 ≤ 10001614370335227^4191*250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        250165215496625301 250000000000000000 10001614370335227 10000000000000000 1024 4191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001614370335227/10000000000000000 : ℝ)) (X := (250165215496625301/250000000000000000 : ℝ)) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3432169990239857/25000000000000000000 : ℝ) ≤ ((5448217277998417521/5450000000000000000 : ℝ)+2*(94356575033/54500000000000 : ℝ)*(1423/12500 : ℝ))^(4191/1024 : ℝ) := by
    rw [show (5448217277998417521/5450000000000000000 : ℝ)+2*(94356575033/54500000000000 : ℝ)*(1423/12500 : ℝ)=(10000670804584897/10000000000000000 : ℝ) by norm_num, show 1+2*(3432169990239857/25000000000000000000 : ℝ)=(12503432169990239857/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(165215496625301/500000000000000000 : ℝ)+(3432169990239857/25000000000000000000 : ℝ) ≤ ((5448217277998417521/5450000000000000000 : ℝ)+(94356575033/54500000000000 : ℝ)*((14109/100000 : ℝ)+(1423/12500 : ℝ)))^(4191/1024 : ℝ) := by
    rw [show (5448217277998417521/5450000000000000000 : ℝ)+(94356575033/54500000000000 : ℝ)*((14109/100000 : ℝ)+(1423/12500 : ℝ))=(5000571293730031/5000000000000000 : ℝ) by norm_num, show 1+(165215496625301/500000000000000000 : ℝ)+(3432169990239857/25000000000000000000 : ℝ)=(25011692944821504907/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(165215496625301/500000000000000000 : ℝ) ≤ ((5448217277998417521/5450000000000000000 : ℝ)+2*(94356575033/54500000000000 : ℝ)*(14109/100000 : ℝ))^(4191/1024 : ℝ) := by
    rw [show (5448217277998417521/5450000000000000000 : ℝ)+2*(94356575033/54500000000000 : ℝ)*(14109/100000 : ℝ)=(10001614370335227/10000000000000000 : ℝ) by norm_num, show 1+2*(165215496625301/500000000000000000 : ℝ)=(250165215496625301/250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5448217277998417521/5450000000000000000 : ℝ)*(X 1 0+X 2 0)+(94356575033/54500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4191/1024 : ℝ)) (lo := (1423/12500 : ℝ)) (hi := (14109/100000 : ℝ)) (c := (5448217277998417521/5450000000000000000 : ℝ)) (alpha := (94356575033/54500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5448217277998417521/5450000000000000000 : ℝ)*(X 0 1+X 2 1)+(94356575033/54500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4191/1024 : ℝ)) (lo := (1423/12500 : ℝ)) (hi := (14109/100000 : ℝ)) (c := (5448217277998417521/5450000000000000000 : ℝ)) (alpha := (94356575033/54500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5448217277998417521/5450000000000000000 : ℝ)*(X 0 2+X 1 2)+(94356575033/54500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4191/1024 : ℝ)) (lo := (1423/12500 : ℝ)) (hi := (14109/100000 : ℝ)) (c := (5448217277998417521/5450000000000000000 : ℝ)) (alpha := (94356575033/54500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-428823053/2000000000 : ℝ)*X 0 0+(5392424551/10000000000 : ℝ)*X 0 1+(526623441/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344629929/10000000000 : ℝ)*X 1 0+(-17250883/78125000 : ℝ)*X 1 1+(5266234469/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336157509/2500000000 : ℝ)*X 2 0+(164569821/312500000 : ℝ)*X 2 1+(-2208113143/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4357941767/10000000000 : ℝ)*X 0 0+(4233044847/10000000000 : ℝ)*X 0 1+(179458531/400000000 : ℝ)*X 0 2+(4357941767/10000000000 : ℝ)*X 1 0+(4233044847/10000000000 : ℝ)*X 1 1+(179458531/400000000 : ℝ)*X 1 2+(4357941767/10000000000 : ℝ)*X 2 0+(4233044847/10000000000 : ℝ)*X 2 1+(179458531/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2144120229/10000000000 : ℝ)*X 0 0+(263327659/500000000 : ℝ)*X 0 1+(5392104521/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312547757/10000000000 : ℝ)*X 1 0+(-83289711/400000000 : ℝ)*X 1 1+(1078420907/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062509553/2000000000 : ℝ)*X 2 0+(5392104533/10000000000 : ℝ)*X 2 1+(-2082242767/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4357951333/10000000000 : ℝ)*X 0 0+(11214557/25000000 : ℝ)*X 0 1+(1058421947/2500000000 : ℝ)*X 0 2+(4357951333/10000000000 : ℝ)*X 1 0+(11214557/25000000 : ℝ)*X 1 1+(1058421947/2500000000 : ℝ)*X 1 2+(4357951333/10000000000 : ℝ)*X 2 0+(11214557/25000000 : ℝ)*X 2 1+(1058421947/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1018154094317396211055675137/136250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (314889391/25000000000000 : ℝ)*(base19) + (1191893247/100000000000000 : ℝ)*(base23) + (157717867/100000000000000 : ℝ)*(lower2) + (66041751/20000000000000 : ℝ)*(upper3) + (36760477/100000000000000 : ℝ)*(lower4) + (2967673276627367/50000000000000 : ℝ)*(major0) + (2967673276627367/50000000000000 : ℝ)*(major1) + (2967673276627367/50000000000000 : ℝ)*(major2) + (7924585333696233/100000000000000 : ℝ)*(sp0) + (3962304462237669/50000000000000 : ℝ)*(sp1) + (1584921798427931/20000000000000 : ℝ)*(sp2) + (493257298515953/12500000000000 : ℝ)*(sp3) + (24850336669/100000000000000 : ℝ)*(sp4) + (1517828703/6250000000000 : ℝ)*(sp7) + (493260334173359/12500000000000 : ℝ)*(f.failure) + (3962305092016451/50000000000000 : ℝ)*(f.sum) + (1572329261141/340625000000000000000000000 : ℝ)*base66 + (3413542303114497207/272500000000000000000000000000000 : ℝ)*base67 + (1376782371744497207/272500000000000000000000000000000 : ℝ)*base69 + (573177121946997207/272500000000000000000000000000000 : ℝ)*base71 + (2228563696189/1362500000000000000000000000 : ℝ)*base74 + (2271381493526997207/272500000000000000000000000000000 : ℝ)*base75 + (1684299529441997207/272500000000000000000000000000000 : ℝ)*base77 + (4183822860831997207/272500000000000000000000000000000 : ℝ)*base79 + (17339511872053/2725000000000000000000000000 : ℝ)*base82 + (2750339/250000000000000000000 : ℝ)*base89 + (2750339/250000000000000000000 : ℝ)*base91 + (2750339/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (257557590040038495338566287/68125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22619751/2000000000000 : ℝ)*(base19) + (584826291/50000000000000 : ℝ)*(base23) + (122220221/100000000000000 : ℝ)*(upper3) + (1807111/20000000000000 : ℝ)*(lower4) + (13725827/12500000000000 : ℝ)*(upper5) + (1491374738868949/25000000000000 : ℝ)*(major0) + (1491374738868949/25000000000000 : ℝ)*(major1) + (1491374738868949/25000000000000 : ℝ)*(major2) + (32579456579/100000000000000 : ℝ)*(sp1) + (34179471281/100000000000000 : ℝ)*(sp2) + (7964868451941911/100000000000000 : ℝ)*(sp4) + (7964834741497781/100000000000000 : ℝ)*(sp5) + (31112629307883/390625000000 : ℝ)*(sp6) + (991532333246903/25000000000000 : ℝ)*(sp7) + (991532333246903/25000000000000 : ℝ)*(f.failure) + (7964868451941911/100000000000000 : ℝ)*(f.sum) + (8126154106057/2725000000000000000000000000 : ℝ)*base66 + (152908937588844571/136250000000000000000000000000000 : ℝ)*base68 + (46127609332405429/136250000000000000000000000000000 : ℝ)*base69 + (1211392449233844571/136250000000000000000000000000000 : ℝ)*base72 + (5534998617757/2725000000000000000000000000 : ℝ)*base74 + (630820128963655429/136250000000000000000000000000000 : ℝ)*base75 + (555304925923844571/136250000000000000000000000000000 : ℝ)*base78 + (3148314371243844571/136250000000000000000000000000000 : ℝ)*base80 + (4224613875943/2725000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (3611563/500000000000000000000 : ℝ)*base89 + (3611563/500000000000000000000 : ℝ)*base91 + (3611563/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1190_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30082221/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14109/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1423/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11409/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7041/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1190_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1190_s7_0 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1072070133/5000000000 : ℝ)*x 0 + (2696084039/5000000000 : ℝ)*x 1 + (658309269/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072070133/5000000000 : ℝ)^8383 ≤ (521336915717/4000000000000 : ℝ)^6335 := by
    have hnat : (1072070133 : ℕ)^8383*4000000000000^6335 ≤ 521336915717^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072070133 5000000000 521336915717 4000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696084039/5000000000 : ℝ)^8383 ≤ (22080911976003/50000000000000 : ℝ)^6335 := by
    have hnat : (2696084039 : ℕ)^8383*50000000000000^6335 ≤ 22080911976003^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696084039 5000000000 22080911976003 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658309269/1250000000 : ℝ)^8383 ≤ (42804753139807/100000000000000 : ℝ)^6335 := by
    have hnat : (658309269 : ℕ)^8383*100000000000000^6335 ≤ 42804753139807^6335*1250000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658309269 1250000000 42804753139807 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1072070133/5000000000 : ℝ), (2696084039/5000000000 : ℝ), (658309269/1250000000 : ℝ)] ![(521336915717/4000000000000 : ℝ), (22080911976003/50000000000000 : ℝ), (42804753139807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1072070133/5000000000 : ℝ)|^8383 ≤ (521336915717/4000000000000 : ℝ)^6335
        have hw : |(-1072070133/5000000000 : ℝ)|=(1072070133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696084039/5000000000 : ℝ)|^8383 ≤ (22080911976003/50000000000000 : ℝ)^6335
        have hw : |(2696084039/5000000000 : ℝ)|=(2696084039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658309269/1250000000 : ℝ)|^8383 ≤ (42804753139807/100000000000000 : ℝ)^6335
        have hw : |(658309269/1250000000 : ℝ)|=(658309269/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s7_1 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068912811/2000000000 : ℝ)*x 0 + (-2207882923/10000000000 : ℝ)*x 1 + (5266474389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068912811/2000000000 : ℝ)^8383 ≤ (4364664436183/10000000000000 : ℝ)^6335 := by
    have hnat : (1068912811 : ℕ)^8383*10000000000000^6335 ≤ 4364664436183^6335*2000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068912811 2000000000 4364664436183 10000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2207882923/10000000000 : ℝ)^8383 ≤ (6774299972639/50000000000000 : ℝ)^6335 := by
    have hnat : (2207882923 : ℕ)^8383*50000000000000^6335 ≤ 6774299972639^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207882923 10000000000 6774299972639 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266474389/10000000000 : ℝ)^8383 ≤ (42804755688827/100000000000000 : ℝ)^6335 := by
    have hnat : (5266474389 : ℕ)^8383*100000000000000^6335 ≤ 42804755688827^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266474389 10000000000 42804755688827 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068912811/2000000000 : ℝ), (-2207882923/10000000000 : ℝ), (5266474389/10000000000 : ℝ)] ![(4364664436183/10000000000000 : ℝ), (6774299972639/50000000000000 : ℝ), (42804755688827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068912811/2000000000 : ℝ)|^8383 ≤ (4364664436183/10000000000000 : ℝ)^6335
        have hw : |(1068912811/2000000000 : ℝ)|=(1068912811/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2207882923/10000000000 : ℝ)|^8383 ≤ (6774299972639/50000000000000 : ℝ)^6335
        have hw : |(-2207882923/10000000000 : ℝ)|=(2207882923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266474389/10000000000 : ℝ)|^8383 ≤ (42804755688827/100000000000000 : ℝ)^6335
        have hw : |(5266474389/10000000000 : ℝ)|=(5266474389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s7_2 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344564091/10000000000 : ℝ)*x 0 + (2633237339/5000000000 : ℝ)*x 1 + (-2207882491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344564091/10000000000 : ℝ)^8383 ≤ (43646644750869/100000000000000 : ℝ)^6335 := by
    have hnat : (5344564091 : ℕ)^8383*100000000000000^6335 ≤ 43646644750869^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344564091 10000000000 43646644750869 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633237339/5000000000 : ℝ)^8383 ≤ (21402379398563/50000000000000 : ℝ)^6335 := by
    have hnat : (2633237339 : ℕ)^8383*50000000000000^6335 ≤ 21402379398563^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633237339 5000000000 21402379398563 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2207882491/10000000000 : ℝ)^8383 ≤ (2709719287463/20000000000000 : ℝ)^6335 := by
    have hnat : (2207882491 : ℕ)^8383*20000000000000^6335 ≤ 2709719287463^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207882491 10000000000 2709719287463 20000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344564091/10000000000 : ℝ), (2633237339/5000000000 : ℝ), (-2207882491/10000000000 : ℝ)] ![(43646644750869/100000000000000 : ℝ), (21402379398563/50000000000000 : ℝ), (2709719287463/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344564091/10000000000 : ℝ)|^8383 ≤ (43646644750869/100000000000000 : ℝ)^6335
        have hw : |(5344564091/10000000000 : ℝ)|=(5344564091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633237339/5000000000 : ℝ)|^8383 ≤ (21402379398563/50000000000000 : ℝ)^6335
        have hw : |(2633237339/5000000000 : ℝ)|=(2633237339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2207882491/10000000000 : ℝ)|^8383 ≤ (2709719287463/20000000000000 : ℝ)^6335
        have hw : |(-2207882491/10000000000 : ℝ)|=(2207882491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s7_3 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (871590901/2000000000 : ℝ)*x 0 + (1058385467/2500000000 : ℝ)*x 1 + (560745359/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871590901/2000000000 : ℝ)^8383 ≤ (3331722284623/10000000000000 : ℝ)^6335 := by
    have hnat : (871590901 : ℕ)^8383*10000000000000^6335 ≤ 3331722284623^6335*2000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871590901 2000000000 3331722284623 10000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1058385467/2500000000 : ℝ)^8383 ≤ (16032211658213/50000000000000 : ℝ)^6335 := by
    have hnat : (1058385467 : ℕ)^8383*50000000000000^6335 ≤ 16032211658213^6335*2500000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058385467 2500000000 16032211658213 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (560745359/1250000000 : ℝ)^8383 ≤ (1730917690883/5000000000000 : ℝ)^6335 := by
    have hnat : (560745359 : ℕ)^8383*5000000000000^6335 ≤ 1730917690883^6335*1250000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560745359 1250000000 1730917690883 5000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871590901/2000000000 : ℝ), (1058385467/2500000000 : ℝ), (560745359/1250000000 : ℝ)] ![(3331722284623/10000000000000 : ℝ), (16032211658213/50000000000000 : ℝ), (1730917690883/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871590901/2000000000 : ℝ)|^8383 ≤ (3331722284623/10000000000000 : ℝ)^6335
        have hw : |(871590901/2000000000 : ℝ)|=(871590901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1058385467/2500000000 : ℝ)|^8383 ≤ (16032211658213/50000000000000 : ℝ)^6335
        have hw : |(1058385467/2500000000 : ℝ)|=(1058385467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(560745359/1250000000 : ℝ)|^8383 ≤ (1730917690883/5000000000000 : ℝ)^6335
        have hw : |(560745359/1250000000 : ℝ)|=(560745359/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s7_4 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-536036143/2500000000 : ℝ)*x 0 + (2633395343/5000000000 : ℝ)*x 1 + (2695925373/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536036143/2500000000 : ℝ)^8383 ≤ (1303345752929/10000000000000 : ℝ)^6335 := by
    have hnat : (536036143 : ℕ)^8383*10000000000000^6335 ≤ 1303345752929^6335*2500000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536036143 2500000000 1303345752929 10000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633395343/5000000000 : ℝ)^8383 ≤ (5351019701187/12500000000000 : ℝ)^6335 := by
    have hnat : (2633395343 : ℕ)^8383*12500000000000^6335 ≤ 5351019701187^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633395343 5000000000 5351019701187 12500000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695925373/5000000000 : ℝ)^8383 ≤ (1766335393649/4000000000000 : ℝ)^6335 := by
    have hnat : (2695925373 : ℕ)^8383*4000000000000^6335 ≤ 1766335393649^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695925373 5000000000 1766335393649 4000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-536036143/2500000000 : ℝ), (2633395343/5000000000 : ℝ), (2695925373/5000000000 : ℝ)] ![(1303345752929/10000000000000 : ℝ), (5351019701187/12500000000000 : ℝ), (1766335393649/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-536036143/2500000000 : ℝ)|^8383 ≤ (1303345752929/10000000000000 : ℝ)^6335
        have hw : |(-536036143/2500000000 : ℝ)|=(536036143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633395343/5000000000 : ℝ)|^8383 ≤ (5351019701187/12500000000000 : ℝ)^6335
        have hw : |(2633395343/5000000000 : ℝ)|=(2633395343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695925373/5000000000 : ℝ)|^8383 ≤ (1766335393649/4000000000000 : ℝ)^6335
        have hw : |(2695925373/5000000000 : ℝ)|=(2695925373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s7_5 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312608411/10000000000 : ℝ)*x 0 + (-2082505861/10000000000 : ℝ)*x 1 + (5391850743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312608411/10000000000 : ℝ)^8383 ≤ (43301644841861/100000000000000 : ℝ)^6335 := by
    have hnat : (5312608411 : ℕ)^8383*100000000000000^6335 ≤ 43301644841861^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312608411 10000000000 43301644841861 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2082505861/10000000000 : ℝ)^8383 ≤ (6269985168921/50000000000000 : ℝ)^6335 := by
    have hnat : (2082505861 : ℕ)^8383*50000000000000^6335 ≤ 6269985168921^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082505861 10000000000 6269985168921 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391850743/10000000000 : ℝ)^8383 ≤ (44158384808713/100000000000000 : ℝ)^6335 := by
    have hnat : (5391850743 : ℕ)^8383*100000000000000^6335 ≤ 44158384808713^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391850743 10000000000 44158384808713 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312608411/10000000000 : ℝ), (-2082505861/10000000000 : ℝ), (5391850743/10000000000 : ℝ)] ![(43301644841861/100000000000000 : ℝ), (6269985168921/50000000000000 : ℝ), (44158384808713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312608411/10000000000 : ℝ)|^8383 ≤ (43301644841861/100000000000000 : ℝ)^6335
        have hw : |(5312608411/10000000000 : ℝ)|=(5312608411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2082505861/10000000000 : ℝ)|^8383 ≤ (6269985168921/50000000000000 : ℝ)^6335
        have hw : |(-2082505861/10000000000 : ℝ)|=(2082505861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391850743/10000000000 : ℝ)|^8383 ≤ (44158384808713/100000000000000 : ℝ)^6335
        have hw : |(5391850743/10000000000 : ℝ)|=(5391850743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s7_6 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062521683/2000000000 : ℝ)*x 0 + (269592537/500000000 : ℝ)*x 1 + (-104125293/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062521683/2000000000 : ℝ)^8383 ≤ (10825411221251/25000000000000 : ℝ)^6335 := by
    have hnat : (1062521683 : ℕ)^8383*25000000000000^6335 ≤ 10825411221251^6335*2000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062521683 2000000000 10825411221251 25000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269592537/500000000 : ℝ)^8383 ≤ (44158384776201/100000000000000 : ℝ)^6335 := by
    have hnat : (269592537 : ℕ)^8383*100000000000000^6335 ≤ 44158384776201^6335*500000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269592537 500000000 44158384776201 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104125293/500000000 : ℝ)^8383 ≤ (6269985164937/50000000000000 : ℝ)^6335 := by
    have hnat : (104125293 : ℕ)^8383*50000000000000^6335 ≤ 6269985164937^6335*500000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104125293 500000000 6269985164937 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062521683/2000000000 : ℝ), (269592537/500000000 : ℝ), (-104125293/500000000 : ℝ)] ![(10825411221251/25000000000000 : ℝ), (44158384776201/100000000000000 : ℝ), (6269985164937/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062521683/2000000000 : ℝ)|^8383 ≤ (10825411221251/25000000000000 : ℝ)^6335
        have hw : |(1062521683/2000000000 : ℝ)|=(1062521683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269592537/500000000 : ℝ)|^8383 ≤ (44158384776201/100000000000000 : ℝ)^6335
        have hw : |(269592537/500000000 : ℝ)|=(269592537/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-104125293/500000000 : ℝ)|^8383 ≤ (6269985164937/50000000000000 : ℝ)^6335
        have hw : |(-104125293/500000000 : ℝ)|=(104125293/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s7_7 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2178981869/5000000000 : ℝ)*x 0 + (4485327881/10000000000 : ℝ)*x 1 + (423417951/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178981869/5000000000 : ℝ)^8383 ≤ (3331731625377/10000000000000 : ℝ)^6335 := by
    have hnat : (2178981869 : ℕ)^8383*10000000000000^6335 ≤ 3331731625377^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178981869 5000000000 3331731625377 10000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4485327881/10000000000 : ℝ)^8383 ≤ (34611869545767/100000000000000 : ℝ)^6335 := by
    have hnat : (4485327881 : ℕ)^8383*100000000000000^6335 ≤ 34611869545767^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485327881 10000000000 34611869545767 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (423417951/1000000000 : ℝ)^8383 ≤ (32070814185337/100000000000000 : ℝ)^6335 := by
    have hnat : (423417951 : ℕ)^8383*100000000000000^6335 ≤ 32070814185337^6335*1000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423417951 1000000000 32070814185337 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178981869/5000000000 : ℝ), (4485327881/10000000000 : ℝ), (423417951/1000000000 : ℝ)] ![(3331731625377/10000000000000 : ℝ), (34611869545767/100000000000000 : ℝ), (32070814185337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178981869/5000000000 : ℝ)|^8383 ≤ (3331731625377/10000000000000 : ℝ)^6335
        have hw : |(2178981869/5000000000 : ℝ)|=(2178981869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4485327881/10000000000 : ℝ)|^8383 ≤ (34611869545767/100000000000000 : ℝ)^6335
        have hw : |(4485327881/10000000000 : ℝ)|=(4485327881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(423417951/1000000000 : ℝ)|^8383 ≤ (32070814185337/100000000000000 : ℝ)^6335
        have hw : |(423417951/1000000000 : ℝ)|=(423417951/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1190_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30082221/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7041/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11409/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5707/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14077/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7041/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11409/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7041/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11409/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7041/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11409/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7041/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11409/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7041/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11409/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7041/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11409/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11409/100000 : ℝ) ^ (4191/1024 : ℝ) ≤ (3463123237638721/25000000000000000000 : ℝ) := by
    have hpowers : (11409/100000 : ℝ)^4191 ≤ (3463123237638721/25000000000000000000 : ℝ)^1024 := by
      have hnat : (11409 : ℕ)^4191*25000000000000000000^1024 ≤ 3463123237638721^1024*100000^4191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11409 100000 3463123237638721 25000000000000000000 4191 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11409/100000 : ℝ)) (X := (3463123237638721/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7041/50000 : ℝ) ^ (4191/1024 : ℝ) ≤ (1311402525242657/4000000000000000000 : ℝ) := by
    have hpowers : (7041/50000 : ℝ)^4191 ≤ (1311402525242657/4000000000000000000 : ℝ)^1024 := by
      have hnat : (7041 : ℕ)^4191*4000000000000000000^1024 ≤ 1311402525242657^1024*50000^4191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7041 50000 1311402525242657 4000000000000000000 4191 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7041/50000 : ℝ)) (X := (1311402525242657/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503463123237638721/12500000000000000000 : ℝ) ≤ (5000338426823183/5000000000000000 : ℝ) ^ (4191/1024 : ℝ) := by
    have hpowers : (12503463123237638721/12500000000000000000 : ℝ)^1024 ≤ (5000338426823183/5000000000000000 : ℝ)^4191 := by
      have hnat : (12503463123237638721 : ℕ)^1024*5000000000000000^4191 ≤ 5000338426823183^4191*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503463123237638721 12500000000000000000 5000338426823183 5000000000000000 1024 4191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000338426823183/5000000000000000 : ℝ)) (X := (12503463123237638721/12500000000000000000 : ℝ)) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046637556081621309/100000000000000000000 : ℝ) ≤ (5000569654549971/5000000000000000 : ℝ) ^ (4191/1024 : ℝ) := by
    have hpowers : (100046637556081621309/100000000000000000000 : ℝ)^1024 ≤ (5000569654549971/5000000000000000 : ℝ)^4191 := by
      have hnat : (100046637556081621309 : ℕ)^1024*5000000000000000^4191 ≤ 5000569654549971^4191*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046637556081621309 100000000000000000000 5000569654549971 5000000000000000 1024 4191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000569654549971/5000000000000000 : ℝ)) (X := (100046637556081621309/100000000000000000000 : ℝ)) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001311402525242657/2000000000000000000 : ℝ) ≤ (5000800882276759/5000000000000000 : ℝ) ^ (4191/1024 : ℝ) := by
    have hpowers : (2001311402525242657/2000000000000000000 : ℝ)^1024 ≤ (5000800882276759/5000000000000000 : ℝ)^4191 := by
      have hnat : (2001311402525242657 : ℕ)^1024*5000000000000000^4191 ≤ 5000800882276759^4191*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001311402525242657 2000000000000000000 5000800882276759 5000000000000000 1024 4191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000800882276759/5000000000000000 : ℝ)) (X := (2001311402525242657/2000000000000000000 : ℝ)) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3463123237638721/25000000000000000000 : ℝ) ≤ ((178141712808380261/178200000000000000 : ℝ)+2*(57806931697/33412500000000 : ℝ)*(11409/100000 : ℝ))^(4191/1024 : ℝ) := by
    rw [show (178141712808380261/178200000000000000 : ℝ)+2*(57806931697/33412500000000 : ℝ)*(11409/100000 : ℝ)=(5000338426823183/5000000000000000 : ℝ) by norm_num, show 1+2*(3463123237638721/25000000000000000000 : ℝ)=(12503463123237638721/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1311402525242657/4000000000000000000 : ℝ)+(3463123237638721/25000000000000000000 : ℝ) ≤ ((178141712808380261/178200000000000000 : ℝ)+(57806931697/33412500000000 : ℝ)*((7041/50000 : ℝ)+(11409/100000 : ℝ)))^(4191/1024 : ℝ) := by
    rw [show (178141712808380261/178200000000000000 : ℝ)+(57806931697/33412500000000 : ℝ)*((7041/50000 : ℝ)+(11409/100000 : ℝ))=(5000569654549971/5000000000000000 : ℝ) by norm_num, show 1+(1311402525242657/4000000000000000000 : ℝ)+(3463123237638721/25000000000000000000 : ℝ)=(100046637556081621309/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1311402525242657/4000000000000000000 : ℝ) ≤ ((178141712808380261/178200000000000000 : ℝ)+2*(57806931697/33412500000000 : ℝ)*(7041/50000 : ℝ))^(4191/1024 : ℝ) := by
    rw [show (178141712808380261/178200000000000000 : ℝ)+2*(57806931697/33412500000000 : ℝ)*(7041/50000 : ℝ)=(5000800882276759/5000000000000000 : ℝ) by norm_num, show 1+2*(1311402525242657/4000000000000000000 : ℝ)=(2001311402525242657/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (178141712808380261/178200000000000000 : ℝ)*(X 1 0+X 2 0)+(57806931697/33412500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4191/1024 : ℝ)) (lo := (11409/100000 : ℝ)) (hi := (7041/50000 : ℝ)) (c := (178141712808380261/178200000000000000 : ℝ)) (alpha := (57806931697/33412500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (178141712808380261/178200000000000000 : ℝ)*(X 0 1+X 2 1)+(57806931697/33412500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4191/1024 : ℝ)) (lo := (11409/100000 : ℝ)) (hi := (7041/50000 : ℝ)) (c := (178141712808380261/178200000000000000 : ℝ)) (alpha := (57806931697/33412500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (178141712808380261/178200000000000000 : ℝ)*(X 0 2+X 1 2)+(57806931697/33412500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4191/1024 : ℝ)) (lo := (11409/100000 : ℝ)) (hi := (7041/50000 : ℝ)) (c := (178141712808380261/178200000000000000 : ℝ)) (alpha := (57806931697/33412500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1072070133/5000000000 : ℝ)*X 0 0+(2696084039/5000000000 : ℝ)*X 0 1+(658309269/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068912811/2000000000 : ℝ)*X 1 0+(-2207882923/10000000000 : ℝ)*X 1 1+(5266474389/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344564091/10000000000 : ℝ)*X 2 0+(2633237339/5000000000 : ℝ)*X 2 1+(-2207882491/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((871590901/2000000000 : ℝ)*X 0 0+(1058385467/2500000000 : ℝ)*X 0 1+(560745359/1250000000 : ℝ)*X 0 2+(871590901/2000000000 : ℝ)*X 1 0+(1058385467/2500000000 : ℝ)*X 1 1+(560745359/1250000000 : ℝ)*X 1 2+(871590901/2000000000 : ℝ)*X 2 0+(1058385467/2500000000 : ℝ)*X 2 1+(560745359/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-536036143/2500000000 : ℝ)*X 0 0+(2633395343/5000000000 : ℝ)*X 0 1+(2695925373/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312608411/10000000000 : ℝ)*X 1 0+(-2082505861/10000000000 : ℝ)*X 1 1+(5391850743/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062521683/2000000000 : ℝ)*X 2 0+(269592537/500000000 : ℝ)*X 2 1+(-104125293/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2178981869/5000000000 : ℝ)*X 0 0+(4485327881/10000000000 : ℝ)*X 0 1+(423417951/1000000000 : ℝ)*X 0 2+(2178981869/5000000000 : ℝ)*X 1 0+(4485327881/10000000000 : ℝ)*X 1 1+(423417951/1000000000 : ℝ)*X 1 2+(2178981869/5000000000 : ℝ)*X 2 0+(4485327881/10000000000 : ℝ)*X 2 1+(423417951/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3694482507128148716591/375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (600240319/50000000000000 : ℝ)*(base19) + (238573979/25000000000000 : ℝ)*(base23) + (210273373/100000000000000 : ℝ)*(upper3) + (80108101/50000000000000 : ℝ)*(upper4) + (705273737/100000000000000 : ℝ)*(upper5) + (148969371234069/2500000000000 : ℝ)*(major0) + (148969371234069/2500000000000 : ℝ)*(major1) + (148969371234069/2500000000000 : ℝ)*(major2) + (79558469312737/1000000000000 : ℝ)*(sp0) + (3977944661004427/50000000000000 : ℝ)*(sp1) + (318235582727743/4000000000000 : ℝ)*(sp2) + (1980825603918551/50000000000000 : ℝ)*(sp3) + (43591215791/100000000000000 : ℝ)*(sp4) + (764000047/10000000000000 : ℝ)*(sp7) + (990414711959393/25000000000000 : ℝ)*(f.failure) + (7955890522489491/100000000000000 : ℝ)*(f.sum) + (1246612497041/148500000000000000000000000 : ℝ)*base65 + (3424586595115997/148500000000000000000000000000 : ℝ)*base68 + (2236024863868997/148500000000000000000000000000 : ℝ)*base70 + (1415328002446003/148500000000000000000000000000 : ℝ)*base71 + (122496650539/14850000000000000000000000 : ℝ)*base74 + (3778124260288997/148500000000000000000000000000 : ℝ)*base76 + (842135192271497/148500000000000000000000000000 : ℝ)*base78 + (820479104779997/148500000000000000000000000000 : ℝ)*base80 + (106010802883/59400000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (3251853/500000000000000000000 : ℝ)*base89 + (3251853/500000000000000000000 : ℝ)*base91 + (3251853/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1123304404765239031216711/135000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (299373151/20000000000000 : ℝ)*(base19) + (409208793/25000000000000 : ℝ)*(base23) + (164772921/100000000000000 : ℝ)*(upper3) + (30426029/50000000000000 : ℝ)*(lower4) + (169674621/100000000000000 : ℝ)*(upper5) + (5988933204562039/100000000000000 : ℝ)*(major0) + (5988933204562039/100000000000000 : ℝ)*(major1) + (5988933204562039/100000000000000 : ℝ)*(major2) + (41683004543/100000000000000 : ℝ)*(sp1) + (4490922869/10000000000000 : ℝ)*(sp2) + (7996156666521657/100000000000000 : ℝ)*(sp4) + (7996113486651359/100000000000000 : ℝ)*(sp5) + (3998055060228897/50000000000000 : ℝ)*(sp6) + (39817094652433/1000000000000 : ℝ)*(sp7) + (39817094652433/1000000000000 : ℝ)*(f.failure) + (7996156666521657/100000000000000 : ℝ)*(f.sum) + (23546495975231/3341250000000000000000000000 : ℝ)*base65 + (239566915488544537/53460000000000000000000000000000 : ℝ)*base67 + (157545636773344537/53460000000000000000000000000000 : ℝ)*base69 + (452134363699024537/53460000000000000000000000000000 : ℝ)*base71 + (3613422374021/3341250000000000000000000000 : ℝ)*base73 + (22382164159975463/53460000000000000000000000000000 : ℝ)*base76 + (443034141293464537/53460000000000000000000000000000 : ℝ)*base77 + (827151512922664537/53460000000000000000000000000000 : ℝ)*base79 + (15727745619293/6682500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (106307/20000000000000000000 : ℝ)*base90 + (106307/20000000000000000000 : ℝ)*base92 + (106307/20000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1190_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30082221/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7041/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11409/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5707/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14077/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1190_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1190_s8_0 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2144143297/10000000000 : ℝ)*x 0 + (2696060003/5000000000 : ℝ)*x 1 + (210660813/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2144143297/10000000000 : ℝ)^8383 ≤ (13033447273513/100000000000000 : ℝ)^6335 := by
    have hnat : (2144143297 : ℕ)^8383*100000000000000^6335 ≤ 13033447273513^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144143297 10000000000 13033447273513 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696060003/5000000000 : ℝ)^8383 ≤ (44161302963679/100000000000000 : ℝ)^6335 := by
    have hnat : (2696060003 : ℕ)^8383*100000000000000^6335 ≤ 44161302963679^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696060003 5000000000 44161302963679 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210660813/400000000 : ℝ)^8383 ≤ (21402624873837/50000000000000 : ℝ)^6335 := by
    have hnat : (210660813 : ℕ)^8383*50000000000000^6335 ≤ 21402624873837^6335*400000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210660813 400000000 21402624873837 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2144143297/10000000000 : ℝ), (2696060003/5000000000 : ℝ), (210660813/400000000 : ℝ)] ![(13033447273513/100000000000000 : ℝ), (44161302963679/100000000000000 : ℝ), (21402624873837/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2144143297/10000000000 : ℝ)|^8383 ≤ (13033447273513/100000000000000 : ℝ)^6335
        have hw : |(-2144143297/10000000000 : ℝ)|=(2144143297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696060003/5000000000 : ℝ)|^8383 ≤ (44161302963679/100000000000000 : ℝ)^6335
        have hw : |(2696060003/5000000000 : ℝ)|=(2696060003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210660813/400000000 : ℝ)|^8383 ≤ (21402624873837/50000000000000 : ℝ)^6335
        have hw : |(210660813/400000000 : ℝ)|=(210660813/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s8_1 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672276301/5000000000 : ℝ)*x 0 + (-88313491/400000000 : ℝ)*x 1 + (131663009/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672276301/5000000000 : ℝ)^8383 ≤ (8729304118643/20000000000000 : ℝ)^6335 := by
    have hnat : (2672276301 : ℕ)^8383*20000000000000^6335 ≤ 8729304118643^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672276301 5000000000 8729304118643 20000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (88313491/400000000 : ℝ)^8383 ≤ (6774114635893/50000000000000 : ℝ)^6335 := by
    have hnat : (88313491 : ℕ)^8383*50000000000000^6335 ≤ 6774114635893^6335*400000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88313491 400000000 6774114635893 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131663009/250000000 : ℝ)^8383 ≤ (42805250124113/100000000000000 : ℝ)^6335 := by
    have hnat : (131663009 : ℕ)^8383*100000000000000^6335 ≤ 42805250124113^6335*250000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131663009 250000000 42805250124113 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672276301/5000000000 : ℝ), (-88313491/400000000 : ℝ), (131663009/250000000 : ℝ)] ![(8729304118643/20000000000000 : ℝ), (6774114635893/50000000000000 : ℝ), (42805250124113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672276301/5000000000 : ℝ)|^8383 ≤ (8729304118643/20000000000000 : ℝ)^6335
        have hw : |(2672276301/5000000000 : ℝ)|=(2672276301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-88313491/400000000 : ℝ)|^8383 ≤ (6774114635893/50000000000000 : ℝ)^6335
        have hw : |(-88313491/400000000 : ℝ)|=(88313491/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131663009/250000000 : ℝ)|^8383 ≤ (42805250124113/100000000000000 : ℝ)^6335
        have hw : |(131663009/250000000 : ℝ)|=(131663009/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s8_2 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344552603/10000000000 : ℝ)*x 0 + (2633260171/5000000000 : ℝ)*x 1 + (-2207837297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344552603/10000000000 : ℝ)^8383 ≤ (21823260302011/50000000000000 : ℝ)^6335 := by
    have hnat : (5344552603 : ℕ)^8383*50000000000000^6335 ≤ 21823260302011^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344552603 10000000000 21823260302011 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633260171/5000000000 : ℝ)^8383 ≤ (10701312482629/25000000000000 : ℝ)^6335 := by
    have hnat : (2633260171 : ℕ)^8383*25000000000000^6335 ≤ 10701312482629^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633260171 5000000000 10701312482629 25000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2207837297/10000000000 : ℝ)^8383 ≤ (13548229450431/100000000000000 : ℝ)^6335 := by
    have hnat : (2207837297 : ℕ)^8383*100000000000000^6335 ≤ 13548229450431^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207837297 10000000000 13548229450431 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344552603/10000000000 : ℝ), (2633260171/5000000000 : ℝ), (-2207837297/10000000000 : ℝ)] ![(21823260302011/50000000000000 : ℝ), (10701312482629/25000000000000 : ℝ), (13548229450431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344552603/10000000000 : ℝ)|^8383 ≤ (21823260302011/50000000000000 : ℝ)^6335
        have hw : |(5344552603/10000000000 : ℝ)|=(5344552603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633260171/5000000000 : ℝ)|^8383 ≤ (10701312482629/25000000000000 : ℝ)^6335
        have hw : |(2633260171/5000000000 : ℝ)|=(2633260171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2207837297/10000000000 : ℝ)|^8383 ≤ (13548229450431/100000000000000 : ℝ)^6335
        have hw : |(-2207837297/10000000000 : ℝ)|=(2207837297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s8_3 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2178978281/5000000000 : ℝ)*x 0 + (2116818091/5000000000 : ℝ)*x 1 + (4485868269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178978281/5000000000 : ℝ)^8383 ≤ (33317243656287/100000000000000 : ℝ)^6335 := by
    have hnat : (2178978281 : ℕ)^8383*100000000000000^6335 ≤ 33317243656287^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178978281 5000000000 33317243656287 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2116818091/5000000000 : ℝ)^8383 ≤ (8016342143491/25000000000000 : ℝ)^6335 := by
    have hnat : (2116818091 : ℕ)^8383*25000000000000^6335 ≤ 8016342143491^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116818091 5000000000 8016342143491 25000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4485868269/10000000000 : ℝ)^8383 ≤ (17308693875591/50000000000000 : ℝ)^6335 := by
    have hnat : (4485868269 : ℕ)^8383*50000000000000^6335 ≤ 17308693875591^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485868269 10000000000 17308693875591 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178978281/5000000000 : ℝ), (2116818091/5000000000 : ℝ), (4485868269/10000000000 : ℝ)] ![(33317243656287/100000000000000 : ℝ), (8016342143491/25000000000000 : ℝ), (17308693875591/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178978281/5000000000 : ℝ)|^8383 ≤ (33317243656287/100000000000000 : ℝ)^6335
        have hw : |(2178978281/5000000000 : ℝ)|=(2178978281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2116818091/5000000000 : ℝ)|^8383 ≤ (8016342143491/25000000000000 : ℝ)^6335
        have hw : |(2116818091/5000000000 : ℝ)|=(2116818091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4485868269/10000000000 : ℝ)|^8383 ≤ (17308693875591/50000000000000 : ℝ)^6335
        have hw : |(4485868269/10000000000 : ℝ)|=(4485868269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s8_4 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1072074087/5000000000 : ℝ)*x 0 + (658354537/1250000000 : ℝ)*x 1 + (673975351/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072074087/5000000000 : ℝ)^8383 ≤ (3258371625719/25000000000000 : ℝ)^6335 := by
    have hnat : (1072074087 : ℕ)^8383*25000000000000^6335 ≤ 3258371625719^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072074087 5000000000 3258371625719 25000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658354537/1250000000 : ℝ)^8383 ≤ (42808648171611/100000000000000 : ℝ)^6335 := by
    have hnat : (658354537 : ℕ)^8383*100000000000000^6335 ≤ 42808648171611^6335*1250000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658354537 1250000000 42808648171611 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673975351/1250000000 : ℝ)^8383 ≤ (11039466328757/25000000000000 : ℝ)^6335 := by
    have hnat : (673975351 : ℕ)^8383*25000000000000^6335 ≤ 11039466328757^6335*1250000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673975351 1250000000 11039466328757 25000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1072074087/5000000000 : ℝ), (658354537/1250000000 : ℝ), (673975351/1250000000 : ℝ)] ![(3258371625719/25000000000000 : ℝ), (42808648171611/100000000000000 : ℝ), (11039466328757/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1072074087/5000000000 : ℝ)|^8383 ≤ (3258371625719/25000000000000 : ℝ)^6335
        have hw : |(-1072074087/5000000000 : ℝ)|=(1072074087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658354537/1250000000 : ℝ)|^8383 ≤ (42808648171611/100000000000000 : ℝ)^6335
        have hw : |(658354537/1250000000 : ℝ)|=(658354537/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673975351/1250000000 : ℝ)|^8383 ≤ (11039466328757/25000000000000 : ℝ)^6335
        have hw : |(673975351/1250000000 : ℝ)|=(673975351/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s8_5 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656310167/5000000000 : ℝ)*x 0 + (-520638653/2500000000 : ℝ)*x 1 + (673975379/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656310167/5000000000 : ℝ)^8383 ≤ (8660354688027/20000000000000 : ℝ)^6335 := by
    have hnat : (2656310167 : ℕ)^8383*20000000000000^6335 ≤ 8660354688027^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656310167 5000000000 8660354688027 20000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (520638653/2500000000 : ℝ)^8383 ≤ (6270179399811/50000000000000 : ℝ)^6335 := by
    have hnat : (520638653 : ℕ)^8383*50000000000000^6335 ≤ 6270179399811^6335*2500000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520638653 2500000000 6270179399811 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673975379/1250000000 : ℝ)^8383 ≤ (5519733467827/12500000000000 : ℝ)^6335 := by
    have hnat : (673975379 : ℕ)^8383*12500000000000^6335 ≤ 5519733467827^6335*1250000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673975379 1250000000 5519733467827 12500000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656310167/5000000000 : ℝ), (-520638653/2500000000 : ℝ), (673975379/1250000000 : ℝ)] ![(8660354688027/20000000000000 : ℝ), (6270179399811/50000000000000 : ℝ), (5519733467827/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656310167/5000000000 : ℝ)|^8383 ≤ (8660354688027/20000000000000 : ℝ)^6335
        have hw : |(2656310167/5000000000 : ℝ)|=(2656310167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-520638653/2500000000 : ℝ)|^8383 ≤ (6270179399811/50000000000000 : ℝ)^6335
        have hw : |(-520638653/2500000000 : ℝ)|=(520638653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673975379/1250000000 : ℝ)|^8383 ≤ (5519733467827/12500000000000 : ℝ)^6335
        have hw : |(673975379/1250000000 : ℝ)|=(673975379/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s8_6 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062524099/2000000000 : ℝ)*x 0 + (2695901413/5000000000 : ℝ)*x 1 + (-520638669/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062524099/2000000000 : ℝ)^8383 ≤ (21650887588319/50000000000000 : ℝ)^6335 := by
    have hnat : (1062524099 : ℕ)^8383*50000000000000^6335 ≤ 21650887588319^6335*2000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062524099 2000000000 21650887588319 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695901413/5000000000 : ℝ)^8383 ≤ (22078932755051/50000000000000 : ℝ)^6335 := by
    have hnat : (2695901413 : ℕ)^8383*50000000000000^6335 ≤ 22078932755051^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695901413 5000000000 22078932755051 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (520638669/2500000000 : ℝ)^8383 ≤ (6270179654797/50000000000000 : ℝ)^6335 := by
    have hnat : (520638669 : ℕ)^8383*50000000000000^6335 ≤ 6270179654797^6335*2500000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520638669 2500000000 6270179654797 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062524099/2000000000 : ℝ), (2695901413/5000000000 : ℝ), (-520638669/2500000000 : ℝ)] ![(21650887588319/50000000000000 : ℝ), (22078932755051/50000000000000 : ℝ), (6270179654797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062524099/2000000000 : ℝ)|^8383 ≤ (21650887588319/50000000000000 : ℝ)^6335
        have hw : |(1062524099/2000000000 : ℝ)|=(1062524099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695901413/5000000000 : ℝ)|^8383 ≤ (22078932755051/50000000000000 : ℝ)^6335
        have hw : |(2695901413/5000000000 : ℝ)|=(2695901413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-520638669/2500000000 : ℝ)|^8383 ≤ (6270179654797/50000000000000 : ℝ)^6335
        have hw : |(-520638669/2500000000 : ℝ)|=(520638669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s8_7 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2178983043/5000000000 : ℝ)*x 0 + (4485233937/10000000000 : ℝ)*x 1 + (84685457/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178983043/5000000000 : ℝ)^8383 ≤ (8329335001951/25000000000000 : ℝ)^6335 := by
    have hnat : (2178983043 : ℕ)^8383*25000000000000^6335 ≤ 8329335001951^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178983043 5000000000 8329335001951 25000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4485233937/10000000000 : ℝ)^8383 ≤ (17305455126371/50000000000000 : ℝ)^6335 := by
    have hnat : (4485233937 : ℕ)^8383*50000000000000^6335 ≤ 17305455126371^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485233937 10000000000 17305455126371 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84685457/200000000 : ℝ)^8383 ≤ (801793743163/2500000000000 : ℝ)^6335 := by
    have hnat : (84685457 : ℕ)^8383*2500000000000^6335 ≤ 801793743163^6335*200000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84685457 200000000 801793743163 2500000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178983043/5000000000 : ℝ), (4485233937/10000000000 : ℝ), (84685457/200000000 : ℝ)] ![(8329335001951/25000000000000 : ℝ), (17305455126371/50000000000000 : ℝ), (801793743163/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178983043/5000000000 : ℝ)|^8383 ≤ (8329335001951/25000000000000 : ℝ)^6335
        have hw : |(2178983043/5000000000 : ℝ)|=(2178983043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4485233937/10000000000 : ℝ)|^8383 ≤ (17305455126371/50000000000000 : ℝ)^6335
        have hw : |(4485233937/10000000000 : ℝ)|=(4485233937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84685457/200000000 : ℝ)|^8383 ≤ (801793743163/2500000000000 : ℝ)^6335
        have hw : |(84685457/200000000 : ℝ)|=(84685457/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1190_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30082221/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14077/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5707/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2283/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3519/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14077/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5707/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14077/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5707/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14077/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5707/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14077/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5707/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14077/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5707/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14077/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5707/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5707/50000 : ℝ) ^ (4191/1024 : ℝ) ≤ (867334778575703/6250000000000000000 : ℝ) := by
    have hpowers : (5707/50000 : ℝ)^4191 ≤ (867334778575703/6250000000000000000 : ℝ)^1024 := by
      have hnat : (5707 : ℕ)^4191*6250000000000000000^1024 ≤ 867334778575703^1024*50000^4191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5707 50000 867334778575703 6250000000000000000 4191 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5707/50000 : ℝ)) (X := (867334778575703/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14077/100000 : ℝ) ^ (4191/1024 : ℝ) ≤ (32737446251637313/100000000000000000000 : ℝ) := by
    have hpowers : (14077/100000 : ℝ)^4191 ≤ (32737446251637313/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14077 : ℕ)^4191*100000000000000000000^1024 ≤ 32737446251637313^1024*100000^4191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14077 100000 32737446251637313 100000000000000000000 4191 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14077/100000 : ℝ)) (X := (32737446251637313/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125867334778575703/3125000000000000000 : ℝ) ≤ (10000678068387337/10000000000000000 : ℝ) ^ (4191/1024 : ℝ) := by
    have hpowers : (3125867334778575703/3125000000000000000 : ℝ)^1024 ≤ (10000678068387337/10000000000000000 : ℝ)^4191 := by
      have hnat : (3125867334778575703 : ℕ)^1024*10000000000000000^4191 ≤ 10000678068387337^4191*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125867334778575703 3125000000000000000 10000678068387337 10000000000000000 1024 4191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000678068387337/10000000000000000 : ℝ)) (X := (3125867334778575703/3125000000000000000 : ℝ)) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046614802708848561/100000000000000000000 : ℝ) ≤ (5000569376677771/5000000000000000 : ℝ) ^ (4191/1024 : ℝ) := by
    have hpowers : (100046614802708848561/100000000000000000000 : ℝ)^1024 ≤ (5000569376677771/5000000000000000 : ℝ)^4191 := by
      have hnat : (100046614802708848561 : ℕ)^1024*5000000000000000^4191 ≤ 5000569376677771^4191*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046614802708848561 100000000000000000000 5000569376677771 5000000000000000 1024 4191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000569376677771/5000000000000000 : ℝ)) (X := (100046614802708848561/100000000000000000000 : ℝ)) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032737446251637313/50000000000000000000 : ℝ) ≤ (10001599438323747/10000000000000000 : ℝ) ^ (4191/1024 : ℝ) := by
    have hpowers : (50032737446251637313/50000000000000000000 : ℝ)^1024 ≤ (10001599438323747/10000000000000000 : ℝ)^4191 := by
      have hnat : (50032737446251637313 : ℕ)^1024*10000000000000000^4191 ≤ 10001599438323747^4191*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032737446251637313 50000000000000000000 10001599438323747 10000000000000000 1024 4191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001599438323747/10000000000000000 : ℝ)) (X := (50032737446251637313/50000000000000000000 : ℝ)) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(867334778575703/6250000000000000000 : ℝ) ≤ ((26621289179661294691/26630000000000000000 : ℝ)+2*(92136993641/53260000000000 : ℝ)*(5707/50000 : ℝ))^(4191/1024 : ℝ) := by
    rw [show (26621289179661294691/26630000000000000000 : ℝ)+2*(92136993641/53260000000000 : ℝ)*(5707/50000 : ℝ)=(10000678068387337/10000000000000000 : ℝ) by norm_num, show 1+2*(867334778575703/6250000000000000000 : ℝ)=(3125867334778575703/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32737446251637313/100000000000000000000 : ℝ)+(867334778575703/6250000000000000000 : ℝ) ≤ ((26621289179661294691/26630000000000000000 : ℝ)+(92136993641/53260000000000 : ℝ)*((14077/100000 : ℝ)+(5707/50000 : ℝ)))^(4191/1024 : ℝ) := by
    rw [show (26621289179661294691/26630000000000000000 : ℝ)+(92136993641/53260000000000 : ℝ)*((14077/100000 : ℝ)+(5707/50000 : ℝ))=(5000569376677771/5000000000000000 : ℝ) by norm_num, show 1+(32737446251637313/100000000000000000000 : ℝ)+(867334778575703/6250000000000000000 : ℝ)=(100046614802708848561/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32737446251637313/100000000000000000000 : ℝ) ≤ ((26621289179661294691/26630000000000000000 : ℝ)+2*(92136993641/53260000000000 : ℝ)*(14077/100000 : ℝ))^(4191/1024 : ℝ) := by
    rw [show (26621289179661294691/26630000000000000000 : ℝ)+2*(92136993641/53260000000000 : ℝ)*(14077/100000 : ℝ)=(10001599438323747/10000000000000000 : ℝ) by norm_num, show 1+2*(32737446251637313/100000000000000000000 : ℝ)=(50032737446251637313/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26621289179661294691/26630000000000000000 : ℝ)*(X 1 0+X 2 0)+(92136993641/53260000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4191/1024 : ℝ)) (lo := (5707/50000 : ℝ)) (hi := (14077/100000 : ℝ)) (c := (26621289179661294691/26630000000000000000 : ℝ)) (alpha := (92136993641/53260000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26621289179661294691/26630000000000000000 : ℝ)*(X 0 1+X 2 1)+(92136993641/53260000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4191/1024 : ℝ)) (lo := (5707/50000 : ℝ)) (hi := (14077/100000 : ℝ)) (c := (26621289179661294691/26630000000000000000 : ℝ)) (alpha := (92136993641/53260000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26621289179661294691/26630000000000000000 : ℝ)*(X 0 2+X 1 2)+(92136993641/53260000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4191/1024 : ℝ)) (lo := (5707/50000 : ℝ)) (hi := (14077/100000 : ℝ)) (c := (26621289179661294691/26630000000000000000 : ℝ)) (alpha := (92136993641/53260000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2144143297/10000000000 : ℝ)*X 0 0+(2696060003/5000000000 : ℝ)*X 0 1+(210660813/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672276301/5000000000 : ℝ)*X 1 0+(-88313491/400000000 : ℝ)*X 1 1+(131663009/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344552603/10000000000 : ℝ)*X 2 0+(2633260171/5000000000 : ℝ)*X 2 1+(-2207837297/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2178978281/5000000000 : ℝ)*X 0 0+(2116818091/5000000000 : ℝ)*X 0 1+(4485868269/10000000000 : ℝ)*X 0 2+(2178978281/5000000000 : ℝ)*X 1 0+(2116818091/5000000000 : ℝ)*X 1 1+(4485868269/10000000000 : ℝ)*X 1 2+(2178978281/5000000000 : ℝ)*X 2 0+(2116818091/5000000000 : ℝ)*X 2 1+(4485868269/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1072074087/5000000000 : ℝ)*X 0 0+(658354537/1250000000 : ℝ)*X 0 1+(673975351/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656310167/5000000000 : ℝ)*X 1 0+(-520638653/2500000000 : ℝ)*X 1 1+(673975379/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062524099/2000000000 : ℝ)*X 2 0+(2695901413/5000000000 : ℝ)*X 2 1+(-520638669/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2178983043/5000000000 : ℝ)*X 0 0+(4485233937/10000000000 : ℝ)*X 0 1+(84685457/200000000 : ℝ)*X 0 2+(2178983043/5000000000 : ℝ)*X 1 0+(4485233937/10000000000 : ℝ)*X 1 1+(84685457/200000000 : ℝ)*X 1 2+(2178983043/5000000000 : ℝ)*X 2 0+(4485233937/10000000000 : ℝ)*X 2 1+(84685457/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1327648693084370897290857039/166437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (154923657/10000000000000 : ℝ)*(base19) + (296205921/20000000000000 : ℝ)*(base23) + (37249761/100000000000000 : ℝ)*(lower2) + (223739407/100000000000000 : ℝ)*(upper3) + (136521211/100000000000000 : ℝ)*(upper5) + (1490817531127843/25000000000000 : ℝ)*(major0) + (1490817531127843/25000000000000 : ℝ)*(major1) + (1490817531127843/25000000000000 : ℝ)*(major2) + (796184957674037/10000000000000 : ℝ)*(sp0) + (497618182935757/6250000000000 : ℝ)*(sp1) + (7961890995179077/100000000000000 : ℝ)*(sp2) + (158584957392739/4000000000000 : ℝ)*(sp3) + (5362433539/12500000000000 : ℝ)*(sp4) + (5893025057/25000000000000 : ℝ)*(sp7) + (1982323753459351/50000000000000 : ℝ)*(f.failure) + (3980946238104341/50000000000000 : ℝ)*(f.sum) + (42932171311/332875000000000000000000000 : ℝ)*base66 + (9102764628563818487/665750000000000000000000000000000 : ℝ)*base68 + (11260277472406068487/665750000000000000000000000000000 : ℝ)*base70 + (3497210427516818487/665750000000000000000000000000000 : ℝ)*base72 + (2541153424417/1331500000000000000000000000 : ℝ)*base73 + (23775418775096568487/665750000000000000000000000000000 : ℝ)*base76 + (989643648822931513/665750000000000000000000000000000 : ℝ)*base77 + (13673131562615318487/665750000000000000000000000000000 : ℝ)*base80 + (4953805566687/1331500000000000000000000000 : ℝ)*base81 + (8701429/1000000000000000000000 : ℝ)*base90 + (8701429/1000000000000000000000 : ℝ)*base92 + (8701429/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10021778110169303353663499859/1331500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (807202793/50000000000000 : ℝ)*(base19) + (1025816857/50000000000000 : ℝ)*(base23) + (616676107/100000000000000 : ℝ)*(lower1) + (36847141/50000000000000 : ℝ)*(upper2) + (306520491/100000000000000 : ℝ)*(upper3) + (111726839/100000000000000 : ℝ)*(upper5) + (5993373577386683/100000000000000 : ℝ)*(major0) + (5993373577386683/100000000000000 : ℝ)*(major1) + (5993373577386683/100000000000000 : ℝ)*(major2) + (9318170621/100000000000000 : ℝ)*(sp2) + (8002085281069117/100000000000000 : ℝ)*(sp4) + (800208366666353/10000000000000 : ℝ)*(sp5) + (4001036955632391/50000000000000 : ℝ)*(sp6) + (3984661622814807/100000000000000 : ℝ)*(sp7) + (3984661622814807/100000000000000 : ℝ)*(f.failure) + (8002085281069117/100000000000000 : ℝ)*(f.sum) + (71614293369/2663000000000000000000000000 : ℝ)*base66 + (2171916341909500047/2663000000000000000000000000000000 : ℝ)*base68 + (147196300385305499953/2663000000000000000000000000000000 : ℝ)*base69 + (6800153436262500047/2663000000000000000000000000000000 : ℝ)*base72 + (2682179048467/1331500000000000000000000000 : ℝ)*base74 + (29770936110193499953/2663000000000000000000000000000000 : ℝ)*base75 + (40019386187641500047/2663000000000000000000000000000000 : ℝ)*base78 + (37975620283075500047/2663000000000000000000000000000000 : ℝ)*base80 + (1293631682657/26630000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (6246347/2000000000000000000000 : ℝ)*base89 + (6246347/2000000000000000000000 : ℝ)*base91 + (6246347/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1190_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30082221/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14077/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5707/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2283/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3519/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1190_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1190_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30082221/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14109/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1423/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2283/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3519/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1190_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1190_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1190_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30082221/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14109/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1423/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2283/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3519/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1190_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

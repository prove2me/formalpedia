-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1478_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:12:32.837417+00:00
-- url     : https://prove2.me/submissions/58f92131-716a-42fc-8b33-faf2361e2625

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
theorem support_rectangle_w1478_s6_0 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1919439111/10000000000 : ℝ)*x 0 + (2718847223/5000000000 : ℝ)*x 1 + (2607862403/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1919439111/10000000000 : ℝ)^4453 ≤ (1465612567969/12500000000000 : ℝ)^3429 := by
    have hnat : (1919439111 : ℕ)^4453*12500000000000^3429 ≤ 1465612567969^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1919439111 10000000000 1465612567969 12500000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718847223/5000000000 : ℝ)^4453 ≤ (22665844314503/50000000000000 : ℝ)^3429 := by
    have hnat : (2718847223 : ℕ)^4453*50000000000000^3429 ≤ 22665844314503^3429*5000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718847223 5000000000 22665844314503 50000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2607862403/5000000000 : ℝ)^4453 ≤ (42943410813147/100000000000000 : ℝ)^3429 := by
    have hnat : (2607862403 : ℕ)^4453*100000000000000^3429 ≤ 42943410813147^3429*5000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607862403 5000000000 42943410813147 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1919439111/10000000000 : ℝ), (2718847223/5000000000 : ℝ), (2607862403/5000000000 : ℝ)] ![(1465612567969/12500000000000 : ℝ), (22665844314503/50000000000000 : ℝ), (42943410813147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1919439111/10000000000 : ℝ)|^4453 ≤ (1465612567969/12500000000000 : ℝ)^3429
        have hw : |(-1919439111/10000000000 : ℝ)|=(1919439111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718847223/5000000000 : ℝ)|^4453 ≤ (22665844314503/50000000000000 : ℝ)^3429
        have hw : |(2718847223/5000000000 : ℝ)|=(2718847223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2607862403/5000000000 : ℝ)|^4453 ≤ (42943410813147/100000000000000 : ℝ)^3429
        have hw : |(2607862403/5000000000 : ℝ)|=(2607862403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_s6_1 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353412401/10000000000 : ℝ)*x 0 + (-2033202547/10000000000 : ℝ)*x 1 + (5215724749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353412401/10000000000 : ℝ)^4453 ≤ (44421361601533/100000000000000 : ℝ)^3429 := by
    have hnat : (5353412401 : ℕ)^4453*100000000000000^3429 ≤ 44421361601533^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353412401 10000000000 44421361601533 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2033202547/10000000000 : ℝ)^4453 ≤ (1263522817509/10000000000000 : ℝ)^3429 := by
    have hnat : (2033202547 : ℕ)^4453*10000000000000^3429 ≤ 1263522817509^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2033202547 10000000000 1263522817509 10000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215724749/10000000000 : ℝ)^4453 ≤ (42943410203691/100000000000000 : ℝ)^3429 := by
    have hnat : (5215724749 : ℕ)^4453*100000000000000^3429 ≤ 42943410203691^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215724749 10000000000 42943410203691 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353412401/10000000000 : ℝ), (-2033202547/10000000000 : ℝ), (5215724749/10000000000 : ℝ)] ![(44421361601533/100000000000000 : ℝ), (1263522817509/10000000000000 : ℝ), (42943410203691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353412401/10000000000 : ℝ)|^4453 ≤ (44421361601533/100000000000000 : ℝ)^3429
        have hw : |(5353412401/10000000000 : ℝ)|=(5353412401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2033202547/10000000000 : ℝ)|^4453 ≤ (1263522817509/10000000000000 : ℝ)^3429
        have hw : |(-2033202547/10000000000 : ℝ)|=(2033202547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215724749/10000000000 : ℝ)|^4453 ≤ (42943410203691/100000000000000 : ℝ)^3429
        have hw : |(5215724749/10000000000 : ℝ)|=(5215724749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_s6_2 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676706171/5000000000 : ℝ)*x 0 + (5215724811/10000000000 : ℝ)*x 1 + (-406640509/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676706171/5000000000 : ℝ)^4453 ≤ (8884272193153/20000000000000 : ℝ)^3429 := by
    have hnat : (2676706171 : ℕ)^4453*20000000000000^3429 ≤ 8884272193153^3429*5000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676706171 5000000000 8884272193153 20000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215724811/10000000000 : ℝ)^4453 ≤ (2683963179163/6250000000000 : ℝ)^3429 := by
    have hnat : (5215724811 : ℕ)^4453*6250000000000^3429 ≤ 2683963179163^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215724811 10000000000 2683963179163 6250000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (406640509/2000000000 : ℝ)^4453 ≤ (252704563179/2000000000000 : ℝ)^3429 := by
    have hnat : (406640509 : ℕ)^4453*2000000000000^3429 ≤ 252704563179^3429*2000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      406640509 2000000000 252704563179 2000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676706171/5000000000 : ℝ), (5215724811/10000000000 : ℝ), (-406640509/2000000000 : ℝ)] ![(8884272193153/20000000000000 : ℝ), (2683963179163/6250000000000 : ℝ), (252704563179/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676706171/5000000000 : ℝ)|^4453 ≤ (8884272193153/20000000000000 : ℝ)^3429
        have hw : |(2676706171/5000000000 : ℝ)|=(2676706171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215724811/10000000000 : ℝ)|^4453 ≤ (2683963179163/6250000000000 : ℝ)^3429
        have hw : |(5215724811/10000000000 : ℝ)|=(5215724811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-406640509/2000000000 : ℝ)|^4453 ≤ (252704563179/2000000000000 : ℝ)^3429
        have hw : |(-406640509/2000000000 : ℝ)|=(406640509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_s6_3 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4285872697/10000000000 : ℝ)*x 0 + (4046372649/10000000000 : ℝ)*x 1 + (4537672761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4285872697/10000000000 : ℝ)^4453 ≤ (3327786051039/10000000000000 : ℝ)^3429 := by
    have hnat : (4285872697 : ℕ)^4453*10000000000000^3429 ≤ 3327786051039^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4285872697 10000000000 3327786051039 10000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4046372649/10000000000 : ℝ)^4453 ≤ (30883336911377/100000000000000 : ℝ)^3429 := by
    have hnat : (4046372649 : ℕ)^4453*100000000000000^3429 ≤ 30883336911377^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4046372649 10000000000 30883336911377 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4537672761/10000000000 : ℝ)^4453 ≤ (1791940128303/5000000000000 : ℝ)^3429 := by
    have hnat : (4537672761 : ℕ)^4453*5000000000000^3429 ≤ 1791940128303^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4537672761 10000000000 1791940128303 5000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4285872697/10000000000 : ℝ), (4046372649/10000000000 : ℝ), (4537672761/10000000000 : ℝ)] ![(3327786051039/10000000000000 : ℝ), (30883336911377/100000000000000 : ℝ), (1791940128303/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4285872697/10000000000 : ℝ)|^4453 ≤ (3327786051039/10000000000000 : ℝ)^3429
        have hw : |(4285872697/10000000000 : ℝ)|=(4285872697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4046372649/10000000000 : ℝ)|^4453 ≤ (30883336911377/100000000000000 : ℝ)^3429
        have hw : |(4046372649/10000000000 : ℝ)|=(4046372649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4537672761/10000000000 : ℝ)|^4453 ≤ (1791940128303/5000000000000 : ℝ)^3429
        have hw : |(4537672761/10000000000 : ℝ)|=(4537672761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_s6_4 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-479867391/2500000000 : ℝ)*x 0 + (5216859881/10000000000 : ℝ)*x 1 + (339784439/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (479867391/2500000000 : ℝ)^4453 ≤ (5862571059143/50000000000000 : ℝ)^3429 := by
    have hnat : (479867391 : ℕ)^4453*50000000000000^3429 ≤ 5862571059143^3429*2500000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      479867391 2500000000 5862571059143 50000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216859881/10000000000 : ℝ)^4453 ≤ (2684721728531/6250000000000 : ℝ)^3429 := by
    have hnat : (5216859881 : ℕ)^4453*6250000000000^3429 ≤ 2684721728531^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216859881 10000000000 2684721728531 6250000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339784439/625000000 : ℝ)^4453 ≤ (45319310209003/100000000000000 : ℝ)^3429 := by
    have hnat : (339784439 : ℕ)^4453*100000000000000^3429 ≤ 45319310209003^3429*625000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339784439 625000000 45319310209003 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-479867391/2500000000 : ℝ), (5216859881/10000000000 : ℝ), (339784439/625000000 : ℝ)] ![(5862571059143/50000000000000 : ℝ), (2684721728531/6250000000000 : ℝ), (45319310209003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-479867391/2500000000 : ℝ)|^4453 ≤ (5862571059143/50000000000000 : ℝ)^3429
        have hw : |(-479867391/2500000000 : ℝ)|=(479867391/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216859881/10000000000 : ℝ)|^4453 ≤ (2684721728531/6250000000000 : ℝ)^3429
        have hw : |(5216859881/10000000000 : ℝ)|=(5216859881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(339784439/625000000 : ℝ)|^4453 ≤ (45319310209003/100000000000000 : ℝ)^3429
        have hw : |(339784439/625000000 : ℝ)|=(339784439/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_s6_5 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295462053/10000000000 : ℝ)*x 0 + (-1812376293/10000000000 : ℝ)*x 1 + (339784439/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295462053/10000000000 : ℝ)^4453 ≤ (4379791665511/10000000000000 : ℝ)^3429 := by
    have hnat : (5295462053 : ℕ)^4453*10000000000000^3429 ≤ 4379791665511^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295462053 10000000000 4379791665511 10000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1812376293/10000000000 : ℝ)^4453 ≤ (1088277312071/10000000000000 : ℝ)^3429 := by
    have hnat : (1812376293 : ℕ)^4453*10000000000000^3429 ≤ 1088277312071^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1812376293 10000000000 1088277312071 10000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339784439/625000000 : ℝ)^4453 ≤ (45319310209003/100000000000000 : ℝ)^3429 := by
    have hnat : (339784439 : ℕ)^4453*100000000000000^3429 ≤ 45319310209003^3429*625000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339784439 625000000 45319310209003 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295462053/10000000000 : ℝ), (-1812376293/10000000000 : ℝ), (339784439/625000000 : ℝ)] ![(4379791665511/10000000000000 : ℝ), (1088277312071/10000000000000 : ℝ), (45319310209003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295462053/10000000000 : ℝ)|^4453 ≤ (4379791665511/10000000000000 : ℝ)^3429
        have hw : |(5295462053/10000000000 : ℝ)|=(5295462053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1812376293/10000000000 : ℝ)|^4453 ≤ (1088277312071/10000000000000 : ℝ)^3429
        have hw : |(-1812376293/10000000000 : ℝ)|=(1812376293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(339784439/625000000 : ℝ)|^4453 ≤ (45319310209003/100000000000000 : ℝ)^3429
        have hw : |(339784439/625000000 : ℝ)|=(339784439/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_s6_6 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295462053/10000000000 : ℝ)*x 0 + (339784439/625000000 : ℝ)*x 1 + (-1812376293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295462053/10000000000 : ℝ)^4453 ≤ (4379791665511/10000000000000 : ℝ)^3429 := by
    have hnat : (5295462053 : ℕ)^4453*10000000000000^3429 ≤ 4379791665511^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295462053 10000000000 4379791665511 10000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339784439/625000000 : ℝ)^4453 ≤ (45319310209003/100000000000000 : ℝ)^3429 := by
    have hnat : (339784439 : ℕ)^4453*100000000000000^3429 ≤ 45319310209003^3429*625000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339784439 625000000 45319310209003 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1812376293/10000000000 : ℝ)^4453 ≤ (1088277312071/10000000000000 : ℝ)^3429 := by
    have hnat : (1812376293 : ℕ)^4453*10000000000000^3429 ≤ 1088277312071^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1812376293 10000000000 1088277312071 10000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295462053/10000000000 : ℝ), (339784439/625000000 : ℝ), (-1812376293/10000000000 : ℝ)] ![(4379791665511/10000000000000 : ℝ), (45319310209003/100000000000000 : ℝ), (1088277312071/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295462053/10000000000 : ℝ)|^4453 ≤ (4379791665511/10000000000000 : ℝ)^3429
        have hw : |(5295462053/10000000000 : ℝ)|=(5295462053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339784439/625000000 : ℝ)|^4453 ≤ (45319310209003/100000000000000 : ℝ)^3429
        have hw : |(339784439/625000000 : ℝ)|=(339784439/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1812376293/10000000000 : ℝ)|^4453 ≤ (1088277312071/10000000000000 : ℝ)^3429
        have hw : |(-1812376293/10000000000 : ℝ)|=(1812376293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_s6_7 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2142970043/5000000000 : ℝ)*x 0 + (4535160357/10000000000 : ℝ)*x 1 + (404890351/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2142970043/5000000000 : ℝ)^4453 ≤ (33278540013379/100000000000000 : ℝ)^3429 := by
    have hnat : (2142970043 : ℕ)^4453*100000000000000^3429 ≤ 33278540013379^3429*5000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142970043 5000000000 33278540013379 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4535160357/10000000000 : ℝ)^4453 ≤ (4476629481087/12500000000000 : ℝ)^3429 := by
    have hnat : (4535160357 : ℕ)^4453*12500000000000^3429 ≤ 4476629481087^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4535160357 10000000000 4476629481087 12500000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (404890351/1000000000 : ℝ)^4453 ≤ (7727106030813/25000000000000 : ℝ)^3429 := by
    have hnat : (404890351 : ℕ)^4453*25000000000000^3429 ≤ 7727106030813^3429*1000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404890351 1000000000 7727106030813 25000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2142970043/5000000000 : ℝ), (4535160357/10000000000 : ℝ), (404890351/1000000000 : ℝ)] ![(33278540013379/100000000000000 : ℝ), (4476629481087/12500000000000 : ℝ), (7727106030813/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2142970043/5000000000 : ℝ)|^4453 ≤ (33278540013379/100000000000000 : ℝ)^3429
        have hw : |(2142970043/5000000000 : ℝ)|=(2142970043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4535160357/10000000000 : ℝ)|^4453 ≤ (4476629481087/12500000000000 : ℝ)^3429
        have hw : |(4535160357/10000000000 : ℝ)|=(4535160357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(404890351/1000000000 : ℝ)|^4453 ≤ (7727106030813/25000000000000 : ℝ)^3429
        have hw : |(404890351/1000000000 : ℝ)|=(404890351/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1478_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160668287/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15477/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1347/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (10777/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (619/4000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (1347/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15477/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1347/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15477/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1347/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15477/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1347/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15477/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1347/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15477/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1347/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1347/12500 : ℝ) ^ (4451/1024 : ℝ) ≤ (3114390258827383/50000000000000000000 : ℝ) := by
    have hpowers : (1347/12500 : ℝ)^4451 ≤ (3114390258827383/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1347 : ℕ)^4451*50000000000000000000^1024 ≤ 3114390258827383^1024*12500^4451 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1347 12500 3114390258827383 50000000000000000000 4451 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1347/12500 : ℝ)) (X := (3114390258827383/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4451 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15477/100000 : ℝ) ^ (4451/1024 : ℝ) ≤ (3756107474820209/12500000000000000000 : ℝ) := by
    have hpowers : (15477/100000 : ℝ)^4451 ≤ (3756107474820209/12500000000000000000 : ℝ)^1024 := by
      have hnat : (15477 : ℕ)^4451*12500000000000000000^1024 ≤ 3756107474820209^1024*100000^4451 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15477 100000 3756107474820209 12500000000000000000 4451 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15477/100000 : ℝ)) (X := (3756107474820209/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4451 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003114390258827383/25000000000000000000 : ℝ) ≤ (5000143292864177/5000000000000000 : ℝ) ^ (4451/1024 : ℝ) := by
    have hpowers : (25003114390258827383/25000000000000000000 : ℝ)^1024 ≤ (5000143292864177/5000000000000000 : ℝ)^4451 := by
      have hnat : (25003114390258827383 : ℕ)^1024*5000000000000000^4451 ≤ 5000143292864177^4451*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003114390258827383 25000000000000000000 5000143292864177 5000000000000000 1024 4451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000143292864177/5000000000000000 : ℝ)) (X := (25003114390258827383/25000000000000000000 : ℝ)) (by norm_num) 4451 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018138820158108219/50000000000000000000 : ℝ) ≤ (5000417244627493/5000000000000000 : ℝ) ^ (4451/1024 : ℝ) := by
    have hpowers : (50018138820158108219/50000000000000000000 : ℝ)^1024 ≤ (5000417244627493/5000000000000000 : ℝ)^4451 := by
      have hnat : (50018138820158108219 : ℕ)^1024*5000000000000000^4451 ≤ 5000417244627493^4451*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018138820158108219 50000000000000000000 5000417244627493 5000000000000000 1024 4451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000417244627493/5000000000000000 : ℝ)) (X := (50018138820158108219/50000000000000000000 : ℝ)) (by norm_num) 4451 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253756107474820209/6250000000000000000 : ℝ) ≤ (5000691196390809/5000000000000000 : ℝ) ^ (4451/1024 : ℝ) := by
    have hpowers : (6253756107474820209/6250000000000000000 : ℝ)^1024 ≤ (5000691196390809/5000000000000000 : ℝ)^4451 := by
      have hnat : (6253756107474820209 : ℕ)^1024*5000000000000000^4451 ≤ 5000691196390809^4451*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253756107474820209 6250000000000000000 5000691196390809 5000000000000000 1024 4451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000691196390809/5000000000000000 : ℝ)) (X := (6253756107474820209/6250000000000000000 : ℝ)) (by norm_num) 4451 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3114390258827383/50000000000000000000 : ℝ) ≤ ((1566651294090100643/1567000000000000000 : ℝ)+2*(68487940829/58762500000000 : ℝ)*(1347/12500 : ℝ))^(4451/1024 : ℝ) := by
    rw [show (1566651294090100643/1567000000000000000 : ℝ)+2*(68487940829/58762500000000 : ℝ)*(1347/12500 : ℝ)=(5000143292864177/5000000000000000 : ℝ) by norm_num, show 1+2*(3114390258827383/50000000000000000000 : ℝ)=(25003114390258827383/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3756107474820209/12500000000000000000 : ℝ)+(3114390258827383/50000000000000000000 : ℝ) ≤ ((1566651294090100643/1567000000000000000 : ℝ)+(68487940829/58762500000000 : ℝ)*((15477/100000 : ℝ)+(1347/12500 : ℝ)))^(4451/1024 : ℝ) := by
    rw [show (1566651294090100643/1567000000000000000 : ℝ)+(68487940829/58762500000000 : ℝ)*((15477/100000 : ℝ)+(1347/12500 : ℝ))=(5000417244627493/5000000000000000 : ℝ) by norm_num, show 1+(3756107474820209/12500000000000000000 : ℝ)+(3114390258827383/50000000000000000000 : ℝ)=(50018138820158108219/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3756107474820209/12500000000000000000 : ℝ) ≤ ((1566651294090100643/1567000000000000000 : ℝ)+2*(68487940829/58762500000000 : ℝ)*(15477/100000 : ℝ))^(4451/1024 : ℝ) := by
    rw [show (1566651294090100643/1567000000000000000 : ℝ)+2*(68487940829/58762500000000 : ℝ)*(15477/100000 : ℝ)=(5000691196390809/5000000000000000 : ℝ) by norm_num, show 1+2*(3756107474820209/12500000000000000000 : ℝ)=(6253756107474820209/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1566651294090100643/1567000000000000000 : ℝ)*(X 1 0+X 2 0)+(68487940829/58762500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4451/1024 : ℝ)) (lo := (1347/12500 : ℝ)) (hi := (15477/100000 : ℝ)) (c := (1566651294090100643/1567000000000000000 : ℝ)) (alpha := (68487940829/58762500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1566651294090100643/1567000000000000000 : ℝ)*(X 0 1+X 2 1)+(68487940829/58762500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4451/1024 : ℝ)) (lo := (1347/12500 : ℝ)) (hi := (15477/100000 : ℝ)) (c := (1566651294090100643/1567000000000000000 : ℝ)) (alpha := (68487940829/58762500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1566651294090100643/1567000000000000000 : ℝ)*(X 0 2+X 1 2)+(68487940829/58762500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4451/1024 : ℝ)) (lo := (1347/12500 : ℝ)) (hi := (15477/100000 : ℝ)) (c := (1566651294090100643/1567000000000000000 : ℝ)) (alpha := (68487940829/58762500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1919439111/10000000000 : ℝ)*X 0 0+(2718847223/5000000000 : ℝ)*X 0 1+(2607862403/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353412401/10000000000 : ℝ)*X 1 0+(-2033202547/10000000000 : ℝ)*X 1 1+(5215724749/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676706171/5000000000 : ℝ)*X 2 0+(5215724811/10000000000 : ℝ)*X 2 1+(-406640509/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4285872697/10000000000 : ℝ)*X 0 0+(4046372649/10000000000 : ℝ)*X 0 1+(4537672761/10000000000 : ℝ)*X 0 2+(4285872697/10000000000 : ℝ)*X 1 0+(4046372649/10000000000 : ℝ)*X 1 1+(4537672761/10000000000 : ℝ)*X 1 2+(4285872697/10000000000 : ℝ)*X 2 0+(4046372649/10000000000 : ℝ)*X 2 1+(4537672761/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-479867391/2500000000 : ℝ)*X 0 0+(5216859881/10000000000 : ℝ)*X 0 1+(339784439/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295462053/10000000000 : ℝ)*X 1 0+(-1812376293/10000000000 : ℝ)*X 1 1+(339784439/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295462053/10000000000 : ℝ)*X 2 0+(339784439/625000000 : ℝ)*X 2 1+(-1812376293/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2142970043/5000000000 : ℝ)*X 0 0+(4535160357/10000000000 : ℝ)*X 0 1+(404890351/1000000000 : ℝ)*X 0 2+(2142970043/5000000000 : ℝ)*X 1 0+(4535160357/10000000000 : ℝ)*X 1 1+(404890351/1000000000 : ℝ)*X 1 2+(2142970043/5000000000 : ℝ)*X 2 0+(4535160357/10000000000 : ℝ)*X 2 1+(404890351/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (443229162360011510395047083/39175000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2031473647/100000000000000 : ℝ)*(base19) + (184054293/10000000000000 : ℝ)*(base23) + (75632523/100000000000000 : ℝ)*(lower2) + (143089597/50000000000000 : ℝ)*(upper3) + (87966567/50000000000000 : ℝ)*(upper5) + (1635156705425009/50000000000000 : ℝ)*(major0) + (1635156705425009/50000000000000 : ℝ)*(major1) + (1635156705425009/50000000000000 : ℝ)*(major2) + (56314403792497/1250000000000 : ℝ)*(sp0) + (2252590081067457/50000000000000 : ℝ)*(sp1) + (4505180353065631/100000000000000 : ℝ)*(sp2) + (254428650183097/12500000000000 : ℝ)*(sp3) + (14945104401/50000000000000 : ℝ)*(sp4) + (7524745311/50000000000000 : ℝ)*(sp7) + (2035444250955397/100000000000000 : ℝ)*(f.failure) + (2252591096804281/50000000000000 : ℝ)*(f.sum) + (137045275001/5876250000000000000000000000 : ℝ)*base66 + (2387627185365577639/235050000000000000000000000000000 : ℝ)*base68 + (1728786821923777639/235050000000000000000000000000000 : ℝ)*base70 + (2286690528379477639/235050000000000000000000000000000 : ℝ)*base72 + (826497316153/2938125000000000000000000000 : ℝ)*base74 + (1064400786092677639/235050000000000000000000000000000 : ℝ)*base76 + (1649411048523877639/235050000000000000000000000000000 : ℝ)*base78 + (1396060585091527639/235050000000000000000000000000000 : ℝ)*base80 + (68503863351571/23505000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (50605061/10000000000000000000000 : ℝ)*base90 + (50605061/10000000000000000000000 : ℝ)*base92 + (50605061/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (275150691385166836342110677/39175000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (146108973/12500000000000 : ℝ)*(base19) + (158595073/12500000000000 : ℝ)*(base23) + (194229867/50000000000000 : ℝ)*(lower1) + (18118617/12500000000000 : ℝ)*(upper3) + (225987/500000000000 : ℝ)*(lower4) + (29024349/20000000000000 : ℝ)*(upper5) + (1652086192061413/50000000000000 : ℝ)*(major0) + (1652086192061413/50000000000000 : ℝ)*(major1) + (1652086192061413/50000000000000 : ℝ)*(major2) + (332109673/25000000000000 : ℝ)*(sp2) + (2275913222972677/50000000000000 : ℝ)*(sp4) + (455182527707357/10000000000000 : ℝ)*(sp5) + (2275911924373039/50000000000000 : ℝ)*(sp6) + (2056518088179297/100000000000000 : ℝ)*(sp7) + (2056518088179297/100000000000000 : ℝ)*(f.failure) + (2275913222972677/50000000000000 : ℝ)*(f.sum) + (27768646594199/11752500000000000000000000000 : ℝ)*base66 + (259555270130375677/235050000000000000000000000000000 : ℝ)*base67 + (59314279827774323/235050000000000000000000000000000 : ℝ)*base70 + (12074586362272925677/235050000000000000000000000000000 : ℝ)*base71 + (51312484109563/23505000000000000000000000000 : ℝ)*base74 + (10817574682726974323/235050000000000000000000000000000 : ℝ)*base76 + (1135335424686474323/235050000000000000000000000000000 : ℝ)*base78 + (3224526995630124323/235050000000000000000000000000000 : ℝ)*base80 + (29714874438413/5876250000000000000000000000 : ℝ)*base81 + (2145761/10000000000000000000000 : ℝ)*base90 + (2145761/10000000000000000000000 : ℝ)*base92 + (2145761/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1478_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160668287/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15477/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1347/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10777/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (619/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1478_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1478_s7_0 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-76777701/400000000 : ℝ)*x 0 + (1087536661/2000000000 : ℝ)*x 1 + (5215733553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (76777701/400000000 : ℝ)^4453 ≤ (2344985525187/20000000000000 : ℝ)^3429 := by
    have hnat : (76777701 : ℕ)^4453*20000000000000^3429 ≤ 2344985525187^3429*400000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76777701 400000000 2344985525187 20000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087536661/2000000000 : ℝ)^4453 ≤ (45331568015387/100000000000000 : ℝ)^3429 := by
    have hnat : (1087536661 : ℕ)^4453*100000000000000^3429 ≤ 45331568015387^3429*2000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087536661 2000000000 45331568015387 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215733553/10000000000 : ℝ)^4453 ≤ (10735876084461/25000000000000 : ℝ)^3429 := by
    have hnat : (5215733553 : ℕ)^4453*25000000000000^3429 ≤ 10735876084461^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215733553 10000000000 10735876084461 25000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-76777701/400000000 : ℝ), (1087536661/2000000000 : ℝ), (5215733553/10000000000 : ℝ)] ![(2344985525187/20000000000000 : ℝ), (45331568015387/100000000000000 : ℝ), (10735876084461/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-76777701/400000000 : ℝ)|^4453 ≤ (2344985525187/20000000000000 : ℝ)^3429
        have hw : |(-76777701/400000000 : ℝ)|=(76777701/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1087536661/2000000000 : ℝ)|^4453 ≤ (45331568015387/100000000000000 : ℝ)^3429
        have hw : |(1087536661/2000000000 : ℝ)|=(1087536661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215733553/10000000000 : ℝ)|^4453 ≤ (10735876084461/25000000000000 : ℝ)^3429
        have hw : |(5215733553/10000000000 : ℝ)|=(5215733553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_s7_1 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (6691761/12500000 : ℝ)*x 0 + (-1016597843/5000000000 : ℝ)*x 1 + (5215733557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6691761/12500000 : ℝ)^4453 ≤ (22210661399081/50000000000000 : ℝ)^3429 := by
    have hnat : (6691761 : ℕ)^4453*50000000000000^3429 ≤ 22210661399081^3429*12500000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6691761 12500000 22210661399081 50000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1016597843/5000000000 : ℝ)^4453 ≤ (1579396600631/12500000000000 : ℝ)^3429 := by
    have hnat : (1016597843 : ℕ)^4453*12500000000000^3429 ≤ 1579396600631^3429*5000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016597843 5000000000 1579396600631 12500000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215733557/10000000000 : ℝ)^4453 ≤ (42943504380613/100000000000000 : ℝ)^3429 := by
    have hnat : (5215733557 : ℕ)^4453*100000000000000^3429 ≤ 42943504380613^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215733557 10000000000 42943504380613 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6691761/12500000 : ℝ), (-1016597843/5000000000 : ℝ), (5215733557/10000000000 : ℝ)] ![(22210661399081/50000000000000 : ℝ), (1579396600631/12500000000000 : ℝ), (42943504380613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6691761/12500000 : ℝ)|^4453 ≤ (22210661399081/50000000000000 : ℝ)^3429
        have hw : |(6691761/12500000 : ℝ)|=(6691761/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1016597843/5000000000 : ℝ)|^4453 ≤ (1579396600631/12500000000000 : ℝ)^3429
        have hw : |(-1016597843/5000000000 : ℝ)|=(1016597843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215733557/10000000000 : ℝ)|^4453 ≤ (42943504380613/100000000000000 : ℝ)^3429
        have hw : |(5215733557/10000000000 : ℝ)|=(5215733557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_s7_2 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676704453/5000000000 : ℝ)*x 0 + (2607866863/5000000000 : ℝ)*x 1 + (-2033195321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676704453/5000000000 : ℝ)^4453 ≤ (11105330985097/25000000000000 : ℝ)^3429 := by
    have hnat : (2676704453 : ℕ)^4453*25000000000000^3429 ≤ 11105330985097^3429*5000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676704453 5000000000 11105330985097 25000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2607866863/5000000000 : ℝ)^4453 ≤ (10735876546899/25000000000000 : ℝ)^3429 := by
    have hnat : (2607866863 : ℕ)^4453*25000000000000^3429 ≤ 10735876546899^3429*5000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607866863 5000000000 10735876546899 25000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2033195321/10000000000 : ℝ)^4453 ≤ (2527033971881/20000000000000 : ℝ)^3429 := by
    have hnat : (2033195321 : ℕ)^4453*20000000000000^3429 ≤ 2527033971881^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2033195321 10000000000 2527033971881 20000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676704453/5000000000 : ℝ), (2607866863/5000000000 : ℝ), (-2033195321/10000000000 : ℝ)] ![(11105330985097/25000000000000 : ℝ), (10735876546899/25000000000000 : ℝ), (2527033971881/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676704453/5000000000 : ℝ)|^4453 ≤ (11105330985097/25000000000000 : ℝ)^3429
        have hw : |(2676704453/5000000000 : ℝ)|=(2676704453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2607866863/5000000000 : ℝ)|^4453 ≤ (10735876546899/25000000000000 : ℝ)^3429
        have hw : |(2607866863/5000000000 : ℝ)|=(2607866863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2033195321/10000000000 : ℝ)|^4453 ≤ (2527033971881/20000000000000 : ℝ)^3429
        have hw : |(-2033195321/10000000000 : ℝ)|=(2033195321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_s7_3 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535734271/1250000000 : ℝ)*x 0 + (2023197173/5000000000 : ℝ)*x 1 + (4537650347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535734271/1250000000 : ℝ)^4453 ≤ (33277875342879/100000000000000 : ℝ)^3429 := by
    have hnat : (535734271 : ℕ)^4453*100000000000000^3429 ≤ 33277875342879^3429*1250000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535734271 1250000000 33277875342879 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2023197173/5000000000 : ℝ)^4453 ≤ (30883551963429/100000000000000 : ℝ)^3429 := by
    have hnat : (2023197173 : ℕ)^4453*100000000000000^3429 ≤ 30883551963429^3429*5000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2023197173 5000000000 30883551963429 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4537650347/10000000000 : ℝ)^4453 ≤ (35838572673681/100000000000000 : ℝ)^3429 := by
    have hnat : (4537650347 : ℕ)^4453*100000000000000^3429 ≤ 35838572673681^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4537650347 10000000000 35838572673681 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535734271/1250000000 : ℝ), (2023197173/5000000000 : ℝ), (4537650347/10000000000 : ℝ)] ![(33277875342879/100000000000000 : ℝ), (30883551963429/100000000000000 : ℝ), (35838572673681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535734271/1250000000 : ℝ)|^4453 ≤ (33277875342879/100000000000000 : ℝ)^3429
        have hw : |(535734271/1250000000 : ℝ)|=(535734271/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2023197173/5000000000 : ℝ)|^4453 ≤ (30883551963429/100000000000000 : ℝ)^3429
        have hw : |(2023197173/5000000000 : ℝ)|=(2023197173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4537650347/10000000000 : ℝ)|^4453 ≤ (35838572673681/100000000000000 : ℝ)^3429
        have hw : |(4537650347/10000000000 : ℝ)|=(4537650347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_s7_4 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1919473131/10000000000 : ℝ)*x 0 + (5216868339/10000000000 : ℝ)*x 1 + (679567507/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1919473131/10000000000 : ℝ)^4453 ≤ (366411575447/3125000000000 : ℝ)^3429 := by
    have hnat : (1919473131 : ℕ)^4453*3125000000000^3429 ≤ 366411575447^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1919473131 10000000000 366411575447 3125000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216868339/10000000000 : ℝ)^4453 ≤ (42955638097023/100000000000000 : ℝ)^3429 := by
    have hnat : (5216868339 : ℕ)^4453*100000000000000^3429 ≤ 42955638097023^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216868339 10000000000 42955638097023 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (679567507/1250000000 : ℝ)^4453 ≤ (45319191475757/100000000000000 : ℝ)^3429 := by
    have hnat : (679567507 : ℕ)^4453*100000000000000^3429 ≤ 45319191475757^3429*1250000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679567507 1250000000 45319191475757 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1919473131/10000000000 : ℝ), (5216868339/10000000000 : ℝ), (679567507/1250000000 : ℝ)] ![(366411575447/3125000000000 : ℝ), (42955638097023/100000000000000 : ℝ), (45319191475757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1919473131/10000000000 : ℝ)|^4453 ≤ (366411575447/3125000000000 : ℝ)^3429
        have hw : |(-1919473131/10000000000 : ℝ)|=(1919473131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216868339/10000000000 : ℝ)|^4453 ≤ (42955638097023/100000000000000 : ℝ)^3429
        have hw : |(5216868339/10000000000 : ℝ)|=(5216868339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(679567507/1250000000 : ℝ)|^4453 ≤ (45319191475757/100000000000000 : ℝ)^3429
        have hw : |(679567507/1250000000 : ℝ)|=(679567507/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_s7_5 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4285941181/10000000000 : ℝ)*x 0 + (4535138573/10000000000 : ℝ)*x 1 + (404892493/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4285941181/10000000000 : ℝ)^4453 ≤ (33278551054611/100000000000000 : ℝ)^3429 := by
    have hnat : (4285941181 : ℕ)^4453*100000000000000^3429 ≤ 33278551054611^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4285941181 10000000000 33278551054611 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4535138573/10000000000 : ℝ)^4453 ≤ (35812812454947/100000000000000 : ℝ)^3429 := by
    have hnat : (4535138573 : ℕ)^4453*100000000000000^3429 ≤ 35812812454947^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4535138573 10000000000 35812812454947 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (404892493/1000000000 : ℝ)^4453 ≤ (30908636469433/100000000000000 : ℝ)^3429 := by
    have hnat : (404892493 : ℕ)^4453*100000000000000^3429 ≤ 30908636469433^3429*1000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404892493 1000000000 30908636469433 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4285941181/10000000000 : ℝ), (4535138573/10000000000 : ℝ), (404892493/1000000000 : ℝ)] ![(33278551054611/100000000000000 : ℝ), (35812812454947/100000000000000 : ℝ), (30908636469433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4285941181/10000000000 : ℝ)|^4453 ≤ (33278551054611/100000000000000 : ℝ)^3429
        have hw : |(4285941181/10000000000 : ℝ)|=(4285941181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4535138573/10000000000 : ℝ)|^4453 ≤ (35812812454947/100000000000000 : ℝ)^3429
        have hw : |(4535138573/10000000000 : ℝ)|=(4535138573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(404892493/1000000000 : ℝ)|^4453 ≤ (30908636469433/100000000000000 : ℝ)^3429
        have hw : |(404892493/1000000000 : ℝ)|=(404892493/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1478_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160668287/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (619/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10777/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5389/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (619/4000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (10777/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (619/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10777/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (619/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10777/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (619/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10777/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (619/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10777/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (619/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10777/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10777/100000 : ℝ) ^ (4451/1024 : ℝ) ≤ (6231293390547919/100000000000000000000 : ℝ) := by
    have hpowers : (10777/100000 : ℝ)^4451 ≤ (6231293390547919/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10777 : ℕ)^4451*100000000000000000000^1024 ≤ 6231293390547919^1024*100000^4451 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10777 100000 6231293390547919 100000000000000000000 4451 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10777/100000 : ℝ)) (X := (6231293390547919/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4451 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (619/4000 : ℝ) ^ (4451/1024 : ℝ) ≤ (6006397028440581/20000000000000000000 : ℝ) := by
    have hpowers : (619/4000 : ℝ)^4451 ≤ (6006397028440581/20000000000000000000 : ℝ)^1024 := by
      have hnat : (619 : ℕ)^4451*20000000000000000000^1024 ≤ 6006397028440581^1024*4000^4451 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        619 4000 6006397028440581 20000000000000000000 4451 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (619/4000 : ℝ)) (X := (6006397028440581/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4451 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006231293390547919/50000000000000000000 : ℝ) ≤ (5000143350669951/5000000000000000 : ℝ) ^ (4451/1024 : ℝ) := by
    have hpowers : (50006231293390547919/50000000000000000000 : ℝ)^1024 ≤ (5000143350669951/5000000000000000 : ℝ)^4451 := by
      have hnat : (50006231293390547919 : ℕ)^1024*5000000000000000^4451 ≤ 5000143350669951^4451*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006231293390547919 50000000000000000000 5000143350669951 5000000000000000 1024 4451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000143350669951/5000000000000000 : ℝ)) (X := (50006231293390547919/50000000000000000000 : ℝ)) (by norm_num) 4451 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12504532909816593853/12500000000000000000 : ℝ) ≤ (10000834158939087/10000000000000000 : ℝ) ^ (4451/1024 : ℝ) := by
    have hpowers : (12504532909816593853/12500000000000000000 : ℝ)^1024 ≤ (10000834158939087/10000000000000000 : ℝ)^4451 := by
      have hnat : (12504532909816593853 : ℕ)^1024*10000000000000000^4451 ≤ 10000834158939087^4451*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504532909816593853 12500000000000000000 10000834158939087 10000000000000000 1024 4451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000834158939087/10000000000000000 : ℝ)) (X := (12504532909816593853/12500000000000000000 : ℝ)) (by norm_num) 4451 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006006397028440581/10000000000000000000 : ℝ) ≤ (312543175516821/312500000000000 : ℝ) ^ (4451/1024 : ℝ) := by
    have hpowers : (10006006397028440581/10000000000000000000 : ℝ)^1024 ≤ (312543175516821/312500000000000 : ℝ)^4451 := by
      have hnat : (10006006397028440581 : ℕ)^1024*312500000000000^4451 ≤ 312543175516821^4451*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006006397028440581 10000000000000000000 312543175516821 312500000000000 1024 4451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312543175516821/312500000000000 : ℝ)) (X := (10006006397028440581/10000000000000000000 : ℝ)) (by norm_num) 4451 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6231293390547919/100000000000000000000 : ℝ) ≤ ((7828257836967004351/7830000000000000000 : ℝ)+2*(36497173279/31320000000000 : ℝ)*(10777/100000 : ℝ))^(4451/1024 : ℝ) := by
    rw [show (7828257836967004351/7830000000000000000 : ℝ)+2*(36497173279/31320000000000 : ℝ)*(10777/100000 : ℝ)=(5000143350669951/5000000000000000 : ℝ) by norm_num, show 1+2*(6231293390547919/100000000000000000000 : ℝ)=(50006231293390547919/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6006397028440581/20000000000000000000 : ℝ)+(6231293390547919/100000000000000000000 : ℝ) ≤ ((7828257836967004351/7830000000000000000 : ℝ)+(36497173279/31320000000000 : ℝ)*((619/4000 : ℝ)+(10777/100000 : ℝ)))^(4451/1024 : ℝ) := by
    rw [show (7828257836967004351/7830000000000000000 : ℝ)+(36497173279/31320000000000 : ℝ)*((619/4000 : ℝ)+(10777/100000 : ℝ))=(10000834158939087/10000000000000000 : ℝ) by norm_num, show 1+(6006397028440581/20000000000000000000 : ℝ)+(6231293390547919/100000000000000000000 : ℝ)=(12504532909816593853/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6006397028440581/20000000000000000000 : ℝ) ≤ ((7828257836967004351/7830000000000000000 : ℝ)+2*(36497173279/31320000000000 : ℝ)*(619/4000 : ℝ))^(4451/1024 : ℝ) := by
    rw [show (7828257836967004351/7830000000000000000 : ℝ)+2*(36497173279/31320000000000 : ℝ)*(619/4000 : ℝ)=(312543175516821/312500000000000 : ℝ) by norm_num, show 1+2*(6006397028440581/20000000000000000000 : ℝ)=(10006006397028440581/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7828257836967004351/7830000000000000000 : ℝ)*(X 1 0+X 2 0)+(36497173279/31320000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4451/1024 : ℝ)) (lo := (10777/100000 : ℝ)) (hi := (619/4000 : ℝ)) (c := (7828257836967004351/7830000000000000000 : ℝ)) (alpha := (36497173279/31320000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7828257836967004351/7830000000000000000 : ℝ)*(X 0 1+X 2 1)+(36497173279/31320000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4451/1024 : ℝ)) (lo := (10777/100000 : ℝ)) (hi := (619/4000 : ℝ)) (c := (7828257836967004351/7830000000000000000 : ℝ)) (alpha := (36497173279/31320000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7828257836967004351/7830000000000000000 : ℝ)*(X 0 2+X 1 2)+(36497173279/31320000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4451/1024 : ℝ)) (lo := (10777/100000 : ℝ)) (hi := (619/4000 : ℝ)) (c := (7828257836967004351/7830000000000000000 : ℝ)) (alpha := (36497173279/31320000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-76777701/400000000 : ℝ)*X 0 0+(1087536661/2000000000 : ℝ)*X 0 1+(5215733553/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((6691761/12500000 : ℝ)*X 1 0+(-1016597843/5000000000 : ℝ)*X 1 1+(5215733557/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676704453/5000000000 : ℝ)*X 2 0+(2607866863/5000000000 : ℝ)*X 2 1+(-2033195321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((535734271/1250000000 : ℝ)*X 0 0+(2023197173/5000000000 : ℝ)*X 0 1+(4537650347/10000000000 : ℝ)*X 0 2+(535734271/1250000000 : ℝ)*X 1 0+(2023197173/5000000000 : ℝ)*X 1 1+(4537650347/10000000000 : ℝ)*X 1 2+(535734271/1250000000 : ℝ)*X 2 0+(2023197173/5000000000 : ℝ)*X 2 1+(4537650347/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1919473131/10000000000 : ℝ)*X 0 0+(5216868339/10000000000 : ℝ)*X 0 1+(679567507/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4285941181/10000000000 : ℝ)*X 0 0+(4535138573/10000000000 : ℝ)*X 0 1+(404892493/1000000000 : ℝ)*X 0 2+(4285941181/10000000000 : ℝ)*X 1 0+(4535138573/10000000000 : ℝ)*X 1 1+(404892493/1000000000 : ℝ)*X 1 2+(4285941181/10000000000 : ℝ)*X 2 0+(4535138573/10000000000 : ℝ)*X 2 1+(404892493/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_s7_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16945550508710771167252883/5437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (311918131/50000000000000 : ℝ)*(base19) + (47977323/10000000000000 : ℝ)*(base23) + (62440783/50000000000000 : ℝ)*(lower2) + (510437/2500000000000 : ℝ)*(upper3) + (204788909/100000000000000 : ℝ)*(upper5) + (408821756974501/12500000000000 : ℝ)*(major0) + (408821756974501/12500000000000 : ℝ)*(major1) + (408821756974501/12500000000000 : ℝ)*(major2) + (4505528857497801/100000000000000 : ℝ)*(sp0) + (4505540907410827/100000000000000 : ℝ)*(sp1) + (4505541051473859/100000000000000 : ℝ)*(sp2) + (1017801496419759/50000000000000 : ℝ)*(sp3) + (12673749289/100000000000000 : ℝ)*(sp4) + (3483624631/100000000000000 : ℝ)*(sp5) + (40712129529283/2000000000000 : ℝ)*(f.failure) + (4505541531247089/100000000000000 : ℝ)*(f.sum) + (6569000254783/783000000000000000000000000 : ℝ)*base65 + (248408472549821149/97875000000000000000000000000000 : ℝ)*base68 + (8183500472928851/97875000000000000000000000000000 : ℝ)*base69 + (1061927564657178851/97875000000000000000000000000000 : ℝ)*base71 + (4674057555889/783000000000000000000000000 : ℝ)*base73 + (525004167339678851/97875000000000000000000000000000 : ℝ)*base75 + (1578735884396928851/97875000000000000000000000000000 : ℝ)*base77 + (210618480714071149/97875000000000000000000000000000 : ℝ)*base80 + (502445337451/156600000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (51779/200000000000000000000 : ℝ)*base90 + (51779/200000000000000000000 : ℝ)*base92 + (51779/200000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1478_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160668287/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (619/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10777/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5389/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (619/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1478_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1478_box_0 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-849762259/5000000000 : ℝ)*x 0 + (5406518377/10000000000 : ℝ)*x 1 + (2703259283/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (849762259/5000000000 : ℝ)^4453 ≤ (39105753659/390625000000 : ℝ)^3429 := by
    have hnat : (849762259 : ℕ)^4453*390625000000^3429 ≤ 39105753659^3429*5000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849762259 5000000000 39105753659 390625000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406518377/10000000000 : ℝ)^4453 ≤ (44994462501467/100000000000000 : ℝ)^3429 := by
    have hnat : (5406518377 : ℕ)^4453*100000000000000^3429 ≤ 44994462501467^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406518377 10000000000 44994462501467 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703259283/5000000000 : ℝ)^4453 ≤ (44994464544091/100000000000000 : ℝ)^3429 := by
    have hnat : (2703259283 : ℕ)^4453*100000000000000^3429 ≤ 44994464544091^3429*5000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703259283 5000000000 44994464544091 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-849762259/5000000000 : ℝ), (5406518377/10000000000 : ℝ), (2703259283/5000000000 : ℝ)] ![(39105753659/390625000000 : ℝ), (44994462501467/100000000000000 : ℝ), (44994464544091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-849762259/5000000000 : ℝ)|^4453 ≤ (39105753659/390625000000 : ℝ)^3429
        have hw : |(-849762259/5000000000 : ℝ)|=(849762259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406518377/10000000000 : ℝ)|^4453 ≤ (44994462501467/100000000000000 : ℝ)^3429
        have hw : |(5406518377/10000000000 : ℝ)|=(5406518377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703259283/5000000000 : ℝ)|^4453 ≤ (44994464544091/100000000000000 : ℝ)^3429
        have hw : |(2703259283/5000000000 : ℝ)|=(2703259283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_box_1 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270190277/10000000000 : ℝ)*x 0 + (-944173983/5000000000 : ℝ)*x 1 + (5406518559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270190277/10000000000 : ℝ)^4453 ≤ (43526672343339/100000000000000 : ℝ)^3429 := by
    have hnat : (5270190277 : ℕ)^4453*100000000000000^3429 ≤ 43526672343339^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270190277 10000000000 43526672343339 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (944173983/5000000000 : ℝ)^4453 ≤ (11478863171573/100000000000000 : ℝ)^3429 := by
    have hnat : (944173983 : ℕ)^4453*100000000000000^3429 ≤ 11478863171573^3429*5000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      944173983 5000000000 11478863171573 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406518559/10000000000 : ℝ)^4453 ≤ (44994464468439/100000000000000 : ℝ)^3429 := by
    have hnat : (5406518559 : ℕ)^4453*100000000000000^3429 ≤ 44994464468439^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406518559 10000000000 44994464468439 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270190277/10000000000 : ℝ), (-944173983/5000000000 : ℝ), (5406518559/10000000000 : ℝ)] ![(43526672343339/100000000000000 : ℝ), (11478863171573/100000000000000 : ℝ), (44994464468439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270190277/10000000000 : ℝ)|^4453 ≤ (43526672343339/100000000000000 : ℝ)^3429
        have hw : |(5270190277/10000000000 : ℝ)|=(5270190277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-944173983/5000000000 : ℝ)|^4453 ≤ (11478863171573/100000000000000 : ℝ)^3429
        have hw : |(-944173983/5000000000 : ℝ)|=(944173983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406518559/10000000000 : ℝ)|^4453 ≤ (44994464468439/100000000000000 : ℝ)^3429
        have hw : |(5406518559/10000000000 : ℝ)|=(5406518559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_box_2 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2635095363/5000000000 : ℝ)*x 0 + (2703258807/5000000000 : ℝ)*x 1 + (-37766973/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2635095363/5000000000 : ℝ)^4453 ≤ (21763338579527/50000000000000 : ℝ)^3429 := by
    have hnat : (2635095363 : ℕ)^4453*50000000000000^3429 ≤ 21763338579527^3429*5000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635095363 5000000000 21763338579527 50000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703258807/5000000000 : ℝ)^4453 ≤ (44994454255319/100000000000000 : ℝ)^3429 := by
    have hnat : (2703258807 : ℕ)^4453*100000000000000^3429 ≤ 44994454255319^3429*5000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703258807 5000000000 44994454255319 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (37766973/200000000 : ℝ)^4453 ≤ (11478868571131/100000000000000 : ℝ)^3429 := by
    have hnat : (37766973 : ℕ)^4453*100000000000000^3429 ≤ 11478868571131^3429*200000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37766973 200000000 11478868571131 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2635095363/5000000000 : ℝ), (2703258807/5000000000 : ℝ), (-37766973/200000000 : ℝ)] ![(21763338579527/50000000000000 : ℝ), (44994454255319/100000000000000 : ℝ), (11478868571131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2635095363/5000000000 : ℝ)|^4453 ≤ (21763338579527/50000000000000 : ℝ)^3429
        have hw : |(2635095363/5000000000 : ℝ)|=(2635095363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703258807/5000000000 : ℝ)|^4453 ≤ (44994454255319/100000000000000 : ℝ)^3429
        have hw : |(2703258807/5000000000 : ℝ)|=(2703258807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-37766973/200000000 : ℝ)|^4453 ≤ (11478868571131/100000000000000 : ℝ)^3429
        have hw : |(-37766973/200000000 : ℝ)|=(37766973/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_box_3 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2245288413/5000000000 : ℝ)*x 0 + (4190733891/10000000000 : ℝ)*x 1 + (4190733907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2245288413/5000000000 : ℝ)^4453 ≤ (7071301292771/20000000000000 : ℝ)^3429 := by
    have hnat : (2245288413 : ℕ)^4453*20000000000000^3429 ≤ 7071301292771^3429*5000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245288413 5000000000 7071301292771 20000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4190733891/10000000000 : ℝ)^4453 ≤ (32321746680697/100000000000000 : ℝ)^3429 := by
    have hnat : (4190733891 : ℕ)^4453*100000000000000^3429 ≤ 32321746680697^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4190733891 10000000000 32321746680697 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4190733907/10000000000 : ℝ)^4453 ≤ (32321746840951/100000000000000 : ℝ)^3429 := by
    have hnat : (4190733907 : ℕ)^4453*100000000000000^3429 ≤ 32321746840951^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4190733907 10000000000 32321746840951 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2245288413/5000000000 : ℝ), (4190733891/10000000000 : ℝ), (4190733907/10000000000 : ℝ)] ![(7071301292771/20000000000000 : ℝ), (32321746680697/100000000000000 : ℝ), (32321746840951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2245288413/5000000000 : ℝ)|^4453 ≤ (7071301292771/20000000000000 : ℝ)^3429
        have hw : |(2245288413/5000000000 : ℝ)|=(2245288413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4190733891/10000000000 : ℝ)|^4453 ≤ (32321746680697/100000000000000 : ℝ)^3429
        have hw : |(4190733891/10000000000 : ℝ)|=(4190733891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4190733907/10000000000 : ℝ)|^4453 ≤ (32321746840951/100000000000000 : ℝ)^3429
        have hw : |(4190733907/10000000000 : ℝ)|=(4190733907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_box_4 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1072411491/5000000000 : ℝ)*x 0 + (2621176129/5000000000 : ℝ)*x 1 + (5242352903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072411491/5000000000 : ℝ)^4453 ≤ (2708665167201/20000000000000 : ℝ)^3429 := by
    have hnat : (1072411491 : ℕ)^4453*20000000000000^3429 ≤ 2708665167201^3429*5000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072411491 5000000000 2708665167201 20000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621176129/5000000000 : ℝ)^4453 ≤ (43228333626083/100000000000000 : ℝ)^3429 := by
    have hnat : (2621176129 : ℕ)^4453*100000000000000^3429 ≤ 43228333626083^3429*5000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621176129 5000000000 43228333626083 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242352903/10000000000 : ℝ)^4453 ≤ (5403542566631/12500000000000 : ℝ)^3429 := by
    have hnat : (5242352903 : ℕ)^4453*12500000000000^3429 ≤ 5403542566631^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242352903 10000000000 5403542566631 12500000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1072411491/5000000000 : ℝ), (2621176129/5000000000 : ℝ), (5242352903/10000000000 : ℝ)] ![(2708665167201/20000000000000 : ℝ), (43228333626083/100000000000000 : ℝ), (5403542566631/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1072411491/5000000000 : ℝ)|^4453 ≤ (2708665167201/20000000000000 : ℝ)^3429
        have hw : |(-1072411491/5000000000 : ℝ)|=(1072411491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621176129/5000000000 : ℝ)|^4453 ≤ (43228333626083/100000000000000 : ℝ)^3429
        have hw : |(2621176129/5000000000 : ℝ)|=(2621176129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242352903/10000000000 : ℝ)|^4453 ≤ (5403542566631/12500000000000 : ℝ)^3429
        have hw : |(5242352903/10000000000 : ℝ)|=(5242352903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_box_5 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (84137351/156250000 : ℝ)*x 0 + (-488878789/2500000000 : ℝ)*x 1 + (1048470601/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84137351/156250000 : ℝ)^4453 ≤ (44759778395967/100000000000000 : ℝ)^3429 := by
    have hnat : (84137351 : ℕ)^4453*100000000000000^3429 ≤ 44759778395967^3429*156250000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84137351 156250000 44759778395967 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (488878789/2500000000 : ℝ)^4453 ≤ (12011879960959/100000000000000 : ℝ)^3429 := by
    have hnat : (488878789 : ℕ)^4453*100000000000000^3429 ≤ 12011879960959^3429*2500000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      488878789 2500000000 12011879960959 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048470601/2000000000 : ℝ)^4453 ≤ (1350885675791/3125000000000 : ℝ)^3429 := by
    have hnat : (1048470601 : ℕ)^4453*3125000000000^3429 ≤ 1350885675791^3429*2000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048470601 2000000000 1350885675791 3125000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(84137351/156250000 : ℝ), (-488878789/2500000000 : ℝ), (1048470601/2000000000 : ℝ)] ![(44759778395967/100000000000000 : ℝ), (12011879960959/100000000000000 : ℝ), (1350885675791/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(84137351/156250000 : ℝ)|^4453 ≤ (44759778395967/100000000000000 : ℝ)^3429
        have hw : |(84137351/156250000 : ℝ)|=(84137351/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-488878789/2500000000 : ℝ)|^4453 ≤ (12011879960959/100000000000000 : ℝ)^3429
        have hw : |(-488878789/2500000000 : ℝ)|=(488878789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048470601/2000000000 : ℝ)|^4453 ≤ (1350885675791/3125000000000 : ℝ)^3429
        have hw : |(1048470601/2000000000 : ℝ)|=(1048470601/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_box_6 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5384790907/10000000000 : ℝ)*x 0 + (209694103/400000000 : ℝ)*x 1 + (-391103027/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5384790907/10000000000 : ℝ)^4453 ≤ (895195663559/2000000000000 : ℝ)^3429 := by
    have hnat : (5384790907 : ℕ)^4453*2000000000000^3429 ≤ 895195663559^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384790907 10000000000 895195663559 2000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209694103/400000000 : ℝ)^4453 ≤ (43228337020669/100000000000000 : ℝ)^3429 := by
    have hnat : (209694103 : ℕ)^4453*100000000000000^3429 ≤ 43228337020669^3429*400000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209694103 400000000 43228337020669 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (391103027/2000000000 : ℝ)^4453 ≤ (3002969948361/25000000000000 : ℝ)^3429 := by
    have hnat : (391103027 : ℕ)^4453*25000000000000^3429 ≤ 3002969948361^3429*2000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      391103027 2000000000 3002969948361 25000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5384790907/10000000000 : ℝ), (209694103/400000000 : ℝ), (-391103027/2000000000 : ℝ)] ![(895195663559/2000000000000 : ℝ), (43228337020669/100000000000000 : ℝ), (3002969948361/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5384790907/10000000000 : ℝ)|^4453 ≤ (895195663559/2000000000000 : ℝ)^3429
        have hw : |(5384790907/10000000000 : ℝ)|=(5384790907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209694103/400000000 : ℝ)|^4453 ≤ (43228337020669/100000000000000 : ℝ)^3429
        have hw : |(209694103/400000000 : ℝ)|=(209694103/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-391103027/2000000000 : ℝ)|^4453 ≤ (3002969948361/25000000000000 : ℝ)^3429
        have hw : |(-391103027/2000000000 : ℝ)|=(391103027/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_box_7 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4078921239/10000000000 : ℝ)*x 0 + (274776417/625000000 : ℝ)*x 1 + (137388213/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4078921239/10000000000 : ℝ)^4453 ≤ (3900791513307/12500000000000 : ℝ)^3429 := by
    have hnat : (4078921239 : ℕ)^4453*12500000000000^3429 ≤ 3900791513307^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4078921239 10000000000 3900791513307 12500000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (274776417/625000000 : ℝ)^4453 ≤ (8599208302327/25000000000000 : ℝ)^3429 := by
    have hnat : (274776417 : ℕ)^4453*25000000000000^3429 ≤ 8599208302327^3429*625000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274776417 625000000 8599208302327 25000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137388213/312500000 : ℝ)^4453 ≤ (34396834672383/100000000000000 : ℝ)^3429 := by
    have hnat : (137388213 : ℕ)^4453*100000000000000^3429 ≤ 34396834672383^3429*312500000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137388213 312500000 34396834672383 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4078921239/10000000000 : ℝ), (274776417/625000000 : ℝ), (137388213/312500000 : ℝ)] ![(3900791513307/12500000000000 : ℝ), (8599208302327/25000000000000 : ℝ), (34396834672383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4078921239/10000000000 : ℝ)|^4453 ≤ (3900791513307/12500000000000 : ℝ)^3429
        have hw : |(4078921239/10000000000 : ℝ)|=(4078921239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(274776417/625000000 : ℝ)|^4453 ≤ (8599208302327/25000000000000 : ℝ)^3429
        have hw : |(274776417/625000000 : ℝ)|=(274776417/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(137388213/312500000 : ℝ)|^4453 ≤ (34396834672383/100000000000000 : ℝ)^3429
        have hw : |(137388213/312500000 : ℝ)|=(137388213/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_box_8 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2050917249/10000000000 : ℝ)*x 0 + (2563865153/5000000000 : ℝ)*x 1 + (5427068851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2050917249/10000000000 : ℝ)^4453 ≤ (2555675215047/20000000000000 : ℝ)^3429 := by
    have hnat : (2050917249 : ℕ)^4453*20000000000000^3429 ≤ 2555675215047^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2050917249 10000000000 2555675215047 20000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2563865153/5000000000 : ℝ)^4453 ≤ (1680197421031/4000000000000 : ℝ)^3429 := by
    have hnat : (2563865153 : ℕ)^4453*4000000000000^3429 ≤ 1680197421031^3429*5000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2563865153 5000000000 1680197421031 4000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5427068851/10000000000 : ℝ)^4453 ≤ (45216688381557/100000000000000 : ℝ)^3429 := by
    have hnat : (5427068851 : ℕ)^4453*100000000000000^3429 ≤ 45216688381557^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427068851 10000000000 45216688381557 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2050917249/10000000000 : ℝ), (2563865153/5000000000 : ℝ), (5427068851/10000000000 : ℝ)] ![(2555675215047/20000000000000 : ℝ), (1680197421031/4000000000000 : ℝ), (45216688381557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2050917249/10000000000 : ℝ)|^4453 ≤ (2555675215047/20000000000000 : ℝ)^3429
        have hw : |(-2050917249/10000000000 : ℝ)|=(2050917249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2563865153/5000000000 : ℝ)|^4453 ≤ (1680197421031/4000000000000 : ℝ)^3429
        have hw : |(2563865153/5000000000 : ℝ)|=(2563865153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5427068851/10000000000 : ℝ)|^4453 ≤ (45216688381557/100000000000000 : ℝ)^3429
        have hw : |(5427068851/10000000000 : ℝ)|=(5427068851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_box_9 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5255836867/10000000000 : ℝ)*x 0 + (-1879685029/10000000000 : ℝ)*x 1 + (339191797/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5255836867/10000000000 : ℝ)^4453 ≤ (21686394305263/50000000000000 : ℝ)^3429 := by
    have hnat : (5255836867 : ℕ)^4453*50000000000000^3429 ≤ 21686394305263^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255836867 10000000000 21686394305263 50000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1879685029/10000000000 : ℝ)^4453 ≤ (2282104812577/20000000000000 : ℝ)^3429 := by
    have hnat : (1879685029 : ℕ)^4453*20000000000000^3429 ≤ 2282104812577^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1879685029 10000000000 2282104812577 20000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339191797/625000000 : ℝ)^4453 ≤ (22608343655199/50000000000000 : ℝ)^3429 := by
    have hnat : (339191797 : ℕ)^4453*50000000000000^3429 ≤ 22608343655199^3429*625000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339191797 625000000 22608343655199 50000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5255836867/10000000000 : ℝ), (-1879685029/10000000000 : ℝ), (339191797/625000000 : ℝ)] ![(21686394305263/50000000000000 : ℝ), (2282104812577/20000000000000 : ℝ), (22608343655199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5255836867/10000000000 : ℝ)|^4453 ≤ (21686394305263/50000000000000 : ℝ)^3429
        have hw : |(5255836867/10000000000 : ℝ)|=(5255836867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1879685029/10000000000 : ℝ)|^4453 ≤ (2282104812577/20000000000000 : ℝ)^3429
        have hw : |(-1879685029/10000000000 : ℝ)|=(1879685029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(339191797/625000000 : ℝ)|^4453 ≤ (22608343655199/50000000000000 : ℝ)^3429
        have hw : |(339191797/625000000 : ℝ)|=(339191797/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_box_10 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2627918329/5000000000 : ℝ)*x 0 + (5427069363/10000000000 : ℝ)*x 1 + (-939842237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2627918329/5000000000 : ℝ)^4453 ≤ (21686393185369/50000000000000 : ℝ)^3429 := by
    have hnat : (2627918329 : ℕ)^4453*50000000000000^3429 ≤ 21686393185369^3429*5000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627918329 5000000000 21686393185369 50000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5427069363/10000000000 : ℝ)^4453 ≤ (45216693921287/100000000000000 : ℝ)^3429 := by
    have hnat : (5427069363 : ℕ)^4453*100000000000000^3429 ≤ 45216693921287^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427069363 10000000000 45216693921287 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (939842237/5000000000 : ℝ)^4453 ≤ (11410519687677/100000000000000 : ℝ)^3429 := by
    have hnat : (939842237 : ℕ)^4453*100000000000000^3429 ≤ 11410519687677^3429*5000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      939842237 5000000000 11410519687677 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2627918329/5000000000 : ℝ), (5427069363/10000000000 : ℝ), (-939842237/5000000000 : ℝ)] ![(21686393185369/50000000000000 : ℝ), (45216693921287/100000000000000 : ℝ), (11410519687677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2627918329/5000000000 : ℝ)|^4453 ≤ (21686393185369/50000000000000 : ℝ)^3429
        have hw : |(2627918329/5000000000 : ℝ)|=(2627918329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5427069363/10000000000 : ℝ)|^4453 ≤ (45216693921287/100000000000000 : ℝ)^3429
        have hw : |(5427069363/10000000000 : ℝ)|=(5427069363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-939842237/5000000000 : ℝ)|^4453 ≤ (11410519687677/100000000000000 : ℝ)^3429
        have hw : |(-939842237/5000000000 : ℝ)|=(939842237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_box_11 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2270477343/5000000000 : ℝ)*x 0 + (4164953379/10000000000 : ℝ)*x 1 + (2082476381/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2270477343/5000000000 : ℝ)^4453 ≤ (35872467756097/100000000000000 : ℝ)^3429 := by
    have hnat : (2270477343 : ℕ)^4453*100000000000000^3429 ≤ 35872467756097^3429*5000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2270477343 5000000000 35872467756097 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4164953379/10000000000 : ℝ)^4453 ≤ (32063769195563/100000000000000 : ℝ)^3429 := by
    have hnat : (4164953379 : ℕ)^4453*100000000000000^3429 ≤ 32063769195563^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4164953379 10000000000 32063769195563 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2082476381/5000000000 : ℝ)^4453 ≤ (32063763027131/100000000000000 : ℝ)^3429 := by
    have hnat : (2082476381 : ℕ)^4453*100000000000000^3429 ≤ 32063763027131^3429*5000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082476381 5000000000 32063763027131 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2270477343/5000000000 : ℝ), (4164953379/10000000000 : ℝ), (2082476381/5000000000 : ℝ)] ![(35872467756097/100000000000000 : ℝ), (32063769195563/100000000000000 : ℝ), (32063763027131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2270477343/5000000000 : ℝ)|^4453 ≤ (35872467756097/100000000000000 : ℝ)^3429
        have hw : |(2270477343/5000000000 : ℝ)|=(2270477343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4164953379/10000000000 : ℝ)|^4453 ≤ (32063769195563/100000000000000 : ℝ)^3429
        have hw : |(4164953379/10000000000 : ℝ)|=(4164953379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2082476381/5000000000 : ℝ)|^4453 ≤ (32063763027131/100000000000000 : ℝ)^3429
        have hw : |(2082476381/5000000000 : ℝ)|=(2082476381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_box_12 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-358714727/2000000000 : ℝ)*x 0 + (1379333023/2500000000 : ℝ)*x 1 + (1306840671/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (358714727/2000000000 : ℝ)^4453 ≤ (10736379975999/100000000000000 : ℝ)^3429 := by
    have hnat : (358714727 : ℕ)^4453*100000000000000^3429 ≤ 10736379975999^3429*2000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      358714727 2000000000 10736379975999 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1379333023/2500000000 : ℝ)^4453 ≤ (46195733244953/100000000000000 : ℝ)^3429 := by
    have hnat : (1379333023 : ℕ)^4453*100000000000000^3429 ≤ 46195733244953^3429*2500000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379333023 2500000000 46195733244953 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1306840671/2500000000 : ℝ)^4453 ≤ (1345871461531/3125000000000 : ℝ)^3429 := by
    have hnat : (1306840671 : ℕ)^4453*3125000000000^3429 ≤ 1345871461531^3429*2500000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306840671 2500000000 1345871461531 3125000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-358714727/2000000000 : ℝ), (1379333023/2500000000 : ℝ), (1306840671/2500000000 : ℝ)] ![(10736379975999/100000000000000 : ℝ), (46195733244953/100000000000000 : ℝ), (1345871461531/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-358714727/2000000000 : ℝ)|^4453 ≤ (10736379975999/100000000000000 : ℝ)^3429
        have hw : |(-358714727/2000000000 : ℝ)|=(358714727/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1379333023/2500000000 : ℝ)|^4453 ≤ (46195733244953/100000000000000 : ℝ)^3429
        have hw : |(1379333023/2500000000 : ℝ)|=(1379333023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1306840671/2500000000 : ℝ)|^4453 ≤ (1345871461531/3125000000000 : ℝ)^3429
        have hw : |(1306840671/2500000000 : ℝ)|=(1306840671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_box_13 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5395253547/10000000000 : ℝ)*x 0 + (-1961464381/10000000000 : ℝ)*x 1 + (326710167/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5395253547/10000000000 : ℝ)^4453 ≤ (44872755366841/100000000000000 : ℝ)^3429 := by
    have hnat : (5395253547 : ℕ)^4453*100000000000000^3429 ≤ 44872755366841^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395253547 10000000000 44872755366841 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1961464381/10000000000 : ℝ)^4453 ≤ (12059357969911/100000000000000 : ℝ)^3429 := by
    have hnat : (1961464381 : ℕ)^4453*100000000000000^3429 ≤ 12059357969911^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1961464381 10000000000 12059357969911 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326710167/625000000 : ℝ)^4453 ≤ (215339433203/500000000000 : ℝ)^3429 := by
    have hnat : (326710167 : ℕ)^4453*500000000000^3429 ≤ 215339433203^3429*625000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326710167 625000000 215339433203 500000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5395253547/10000000000 : ℝ), (-1961464381/10000000000 : ℝ), (326710167/625000000 : ℝ)] ![(44872755366841/100000000000000 : ℝ), (12059357969911/100000000000000 : ℝ), (215339433203/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5395253547/10000000000 : ℝ)|^4453 ≤ (44872755366841/100000000000000 : ℝ)^3429
        have hw : |(5395253547/10000000000 : ℝ)|=(5395253547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1961464381/10000000000 : ℝ)|^4453 ≤ (12059357969911/100000000000000 : ℝ)^3429
        have hw : |(-1961464381/10000000000 : ℝ)|=(1961464381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326710167/625000000 : ℝ)|^4453 ≤ (215339433203/500000000000 : ℝ)^3429
        have hw : |(326710167/625000000 : ℝ)|=(326710167/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_box_14 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5395253627/10000000000 : ℝ)*x 0 + (5227362581/10000000000 : ℝ)*x 1 + (-392292879/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5395253627/10000000000 : ℝ)^4453 ≤ (8974551246181/20000000000000 : ℝ)^3429 := by
    have hnat : (5395253627 : ℕ)^4453*20000000000000^3429 ≤ 8974551246181^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395253627 10000000000 8974551246181 20000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5227362581/10000000000 : ℝ)^4453 ≤ (21533942833481/50000000000000 : ℝ)^3429 := by
    have hnat : (5227362581 : ℕ)^4453*50000000000000^3429 ≤ 21533942833481^3429*10000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227362581 10000000000 21533942833481 50000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (392292879/2000000000 : ℝ)^4453 ≤ (12059358081689/100000000000000 : ℝ)^3429 := by
    have hnat : (392292879 : ℕ)^4453*100000000000000^3429 ≤ 12059358081689^3429*2000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      392292879 2000000000 12059358081689 100000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5395253627/10000000000 : ℝ), (5227362581/10000000000 : ℝ), (-392292879/2000000000 : ℝ)] ![(8974551246181/20000000000000 : ℝ), (21533942833481/50000000000000 : ℝ), (12059358081689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5395253627/10000000000 : ℝ)|^4453 ≤ (8974551246181/20000000000000 : ℝ)^3429
        have hw : |(5395253627/10000000000 : ℝ)|=(5395253627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5227362581/10000000000 : ℝ)|^4453 ≤ (21533942833481/50000000000000 : ℝ)^3429
        have hw : |(5227362581/10000000000 : ℝ)|=(5227362581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-392292879/2000000000 : ℝ)|^4453 ≤ (12059358081689/100000000000000 : ℝ)^3429
        have hw : |(-392292879/2000000000 : ℝ)|=(392292879/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1478_box_15 (p : ℝ) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1010118229/2500000000 : ℝ)*x 0 + (883036599/2000000000 : ℝ)*x 1 + (2207591401/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1010118229/2500000000 : ℝ)^4453 ≤ (15412436940719/50000000000000 : ℝ)^3429 := by
    have hnat : (1010118229 : ℕ)^4453*50000000000000^3429 ≤ 15412436940719^3429*2500000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010118229 2500000000 15412436940719 50000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (883036599/2000000000 : ℝ)^4453 ≤ (17293782018059/50000000000000 : ℝ)^3429 := by
    have hnat : (883036599 : ℕ)^4453*50000000000000^3429 ≤ 17293782018059^3429*2000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883036599 2000000000 17293782018059 50000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2207591401/5000000000 : ℝ)^4453 ≤ (6917512414539/20000000000000 : ℝ)^3429 := by
    have hnat : (2207591401 : ℕ)^4453*20000000000000^3429 ≤ 6917512414539^3429*5000000000^4453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207591401 5000000000 6917512414539 20000000000000 4453 3429 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4453/1024 : ℝ)) 4453 3429 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1010118229/2500000000 : ℝ), (883036599/2000000000 : ℝ), (2207591401/5000000000 : ℝ)] ![(15412436940719/50000000000000 : ℝ), (17293782018059/50000000000000 : ℝ), (6917512414539/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1010118229/2500000000 : ℝ)|^4453 ≤ (15412436940719/50000000000000 : ℝ)^3429
        have hw : |(1010118229/2500000000 : ℝ)|=(1010118229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(883036599/2000000000 : ℝ)|^4453 ≤ (17293782018059/50000000000000 : ℝ)^3429
        have hw : |(883036599/2000000000 : ℝ)|=(883036599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2207591401/5000000000 : ℝ)|^4453 ≤ (6917512414539/20000000000000 : ℝ)^3429
        have hw : |(2207591401/5000000000 : ℝ)|=(2207591401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1478_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160668287/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (619/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5389/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(637/1000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14617/25000 : ℝ) ∧ (39973/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (4289/5000 : ℝ) := by
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
  have lower0 : (5389/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (619/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5389/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (619/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5389/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (619/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5389/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (619/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5389/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (619/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5389/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5389/50000 : ℝ) ^ (4451/1024 : ℝ) ≤ (6233807043907489/100000000000000000000 : ℝ) := by
    have hpowers : (5389/50000 : ℝ)^4451 ≤ (6233807043907489/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5389 : ℕ)^4451*100000000000000000000^1024 ≤ 6233807043907489^1024*50000^4451 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5389 50000 6233807043907489 100000000000000000000 4451 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5389/50000 : ℝ)) (X := (6233807043907489/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4451 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (619/4000 : ℝ) ^ (4451/1024 : ℝ) ≤ (6006397028440581/20000000000000000000 : ℝ) := by
    have hpowers : (619/4000 : ℝ)^4451 ≤ (6006397028440581/20000000000000000000 : ℝ)^1024 := by
      have hnat : (619 : ℕ)^4451*20000000000000000000^1024 ≤ 6006397028440581^1024*4000^4451 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        619 4000 6006397028440581 20000000000000000000 4451 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (619/4000 : ℝ)) (X := (6006397028440581/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4451 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006233807043907489/50000000000000000000 : ℝ) ≤ (5000143408493677/5000000000000000 : ℝ) ^ (4451/1024 : ℝ) := by
    have hpowers : (50006233807043907489/50000000000000000000 : ℝ)^1024 ≤ (5000143408493677/5000000000000000 : ℝ)^4451 := by
      have hnat : (50006233807043907489 : ℕ)^1024*5000000000000000^4451 ≤ 5000143408493677^4451*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006233807043907489 50000000000000000000 5000143408493677 5000000000000000 1024 4451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000143408493677/5000000000000000 : ℝ)) (X := (50006233807043907489/50000000000000000000 : ℝ)) (by norm_num) 4451 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018132896093055197/50000000000000000000 : ℝ) ≤ (10000834216752221/10000000000000000 : ℝ) ^ (4451/1024 : ℝ) := by
    have hpowers : (50018132896093055197/50000000000000000000 : ℝ)^1024 ≤ (10000834216752221/10000000000000000 : ℝ)^4451 := by
      have hnat : (50018132896093055197 : ℕ)^1024*10000000000000000^4451 ≤ 10000834216752221^4451*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018132896093055197 50000000000000000000 10000834216752221 10000000000000000 1024 4451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000834216752221/10000000000000000 : ℝ)) (X := (50018132896093055197/50000000000000000000 : ℝ)) (by norm_num) 4451 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006006397028440581/10000000000000000000 : ℝ) ≤ (312543175516159/312500000000000 : ℝ) ^ (4451/1024 : ℝ) := by
    have hpowers : (10006006397028440581/10000000000000000000 : ℝ)^1024 ≤ (312543175516159/312500000000000 : ℝ)^4451 := by
      have hnat : (10006006397028440581 : ℕ)^1024*312500000000000^4451 ≤ 312543175516159^4451*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006006397028440581 10000000000000000000 312543175516159 312500000000000 1024 4451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312543175516159/312500000000000 : ℝ)) (X := (10006006397028440581/10000000000000000000 : ℝ)) (by norm_num) 4451 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6233807043907489/100000000000000000000 : ℝ) ≤ ((23479773715029064343/23485000000000000000 : ℝ)+2*(547399764867/469700000000000 : ℝ)*(5389/50000 : ℝ))^(4451/1024 : ℝ) := by
    rw [show (23479773715029064343/23485000000000000000 : ℝ)+2*(547399764867/469700000000000 : ℝ)*(5389/50000 : ℝ)=(5000143408493677/5000000000000000 : ℝ) by norm_num, show 1+2*(6233807043907489/100000000000000000000 : ℝ)=(50006233807043907489/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6006397028440581/20000000000000000000 : ℝ)+(6233807043907489/100000000000000000000 : ℝ) ≤ ((23479773715029064343/23485000000000000000 : ℝ)+(547399764867/469700000000000 : ℝ)*((619/4000 : ℝ)+(5389/50000 : ℝ)))^(4451/1024 : ℝ) := by
    rw [show (23479773715029064343/23485000000000000000 : ℝ)+(547399764867/469700000000000 : ℝ)*((619/4000 : ℝ)+(5389/50000 : ℝ))=(10000834216752221/10000000000000000 : ℝ) by norm_num, show 1+(6006397028440581/20000000000000000000 : ℝ)+(6233807043907489/100000000000000000000 : ℝ)=(50018132896093055197/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6006397028440581/20000000000000000000 : ℝ) ≤ ((23479773715029064343/23485000000000000000 : ℝ)+2*(547399764867/469700000000000 : ℝ)*(619/4000 : ℝ))^(4451/1024 : ℝ) := by
    rw [show (23479773715029064343/23485000000000000000 : ℝ)+2*(547399764867/469700000000000 : ℝ)*(619/4000 : ℝ)=(312543175516159/312500000000000 : ℝ) by norm_num, show 1+2*(6006397028440581/20000000000000000000 : ℝ)=(10006006397028440581/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23479773715029064343/23485000000000000000 : ℝ)*(X 1 0+X 2 0)+(547399764867/469700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4451/1024 : ℝ)) (lo := (5389/50000 : ℝ)) (hi := (619/4000 : ℝ)) (c := (23479773715029064343/23485000000000000000 : ℝ)) (alpha := (547399764867/469700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23479773715029064343/23485000000000000000 : ℝ)*(X 0 1+X 2 1)+(547399764867/469700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4451/1024 : ℝ)) (lo := (5389/50000 : ℝ)) (hi := (619/4000 : ℝ)) (c := (23479773715029064343/23485000000000000000 : ℝ)) (alpha := (547399764867/469700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23479773715029064343/23485000000000000000 : ℝ)*(X 0 2+X 1 2)+(547399764867/469700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4451/1024 : ℝ)) (lo := (5389/50000 : ℝ)) (hi := (619/4000 : ℝ)) (c := (23479773715029064343/23485000000000000000 : ℝ)) (alpha := (547399764867/469700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-849762259/5000000000 : ℝ)*X 0 0+(5406518377/10000000000 : ℝ)*X 0 1+(2703259283/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5270190277/10000000000 : ℝ)*X 1 0+(-944173983/5000000000 : ℝ)*X 1 1+(5406518559/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2635095363/5000000000 : ℝ)*X 2 0+(2703258807/5000000000 : ℝ)*X 2 1+(-37766973/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2245288413/5000000000 : ℝ)*X 0 0+(4190733891/10000000000 : ℝ)*X 0 1+(4190733907/10000000000 : ℝ)*X 0 2+(2245288413/5000000000 : ℝ)*X 1 0+(4190733891/10000000000 : ℝ)*X 1 1+(4190733907/10000000000 : ℝ)*X 1 2+(2245288413/5000000000 : ℝ)*X 2 0+(4190733891/10000000000 : ℝ)*X 2 1+(4190733907/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1072411491/5000000000 : ℝ)*X 0 0+(2621176129/5000000000 : ℝ)*X 0 1+(5242352903/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((84137351/156250000 : ℝ)*X 1 0+(-488878789/2500000000 : ℝ)*X 1 1+(1048470601/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5384790907/10000000000 : ℝ)*X 2 0+(209694103/400000000 : ℝ)*X 2 1+(-391103027/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4078921239/10000000000 : ℝ)*X 0 0+(274776417/625000000 : ℝ)*X 0 1+(137388213/312500000 : ℝ)*X 0 2+(4078921239/10000000000 : ℝ)*X 1 0+(274776417/625000000 : ℝ)*X 1 1+(137388213/312500000 : ℝ)*X 1 2+(4078921239/10000000000 : ℝ)*X 2 0+(274776417/625000000 : ℝ)*X 2 1+(137388213/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2050917249/10000000000 : ℝ)*X 0 0+(2563865153/5000000000 : ℝ)*X 0 1+(5427068851/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5255836867/10000000000 : ℝ)*X 1 0+(-1879685029/10000000000 : ℝ)*X 1 1+(339191797/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2627918329/5000000000 : ℝ)*X 2 0+(5427069363/10000000000 : ℝ)*X 2 1+(-939842237/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2270477343/5000000000 : ℝ)*X 0 0+(4164953379/10000000000 : ℝ)*X 0 1+(2082476381/5000000000 : ℝ)*X 0 2+(2270477343/5000000000 : ℝ)*X 1 0+(4164953379/10000000000 : ℝ)*X 1 1+(2082476381/5000000000 : ℝ)*X 1 2+(2270477343/5000000000 : ℝ)*X 2 0+(4164953379/10000000000 : ℝ)*X 2 1+(2082476381/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-358714727/2000000000 : ℝ)*X 0 0+(1379333023/2500000000 : ℝ)*X 0 1+(1306840671/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5395253547/10000000000 : ℝ)*X 1 0+(-1961464381/10000000000 : ℝ)*X 1 1+(326710167/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5395253627/10000000000 : ℝ)*X 2 0+(5227362581/10000000000 : ℝ)*X 2 1+(-392292879/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1010118229/2500000000 : ℝ)*X 0 0+(883036599/2000000000 : ℝ)*X 0 1+(2207591401/5000000000 : ℝ)*X 0 2+(1010118229/2500000000 : ℝ)*X 1 0+(883036599/2000000000 : ℝ)*X 1 1+(2207591401/5000000000 : ℝ)*X 1 2+(1010118229/2500000000 : ℝ)*X 2 0+(883036599/2000000000 : ℝ)*X 2 1+(2207591401/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1478_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-637/1000 : ℝ) ≤ (-278676660798357420121455841173/437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (39035743/100000000000000 : ℝ)*(lower2) + (61342717/100000000000000 : ℝ)*(lower3) + (233049/1250000000000 : ℝ)*(upper5) + (543178068080727/25000000000000 : ℝ)*(major0) + (543178068080727/25000000000000 : ℝ)*(major1) + (543178068080727/25000000000000 : ℝ)*(major2) + (141174331/6250000000000 : ℝ)*(sp2) + (376794500212537/12500000000000 : ℝ)*(sp4) + (301429456934719/10000000000000 : ℝ)*(sp5) + (1507178944202399/50000000000000 : ℝ)*(sp6) + (33806068791407/2500000000000 : ℝ)*(sp7) + (4145493797/100000000000000 : ℝ)*(sp12) + (65577846903/100000000000000 : ℝ)*(sp13) + (10830656967/20000000000000 : ℝ)*(sp15) + (270459380988223/20000000000000 : ℝ)*(f.failure) + (1507180073597047/50000000000000 : ℝ)*(f.sum) + (64319172592931/23485000000000000000000000000 : ℝ)*base65 + (4109125152283042361/587125000000000000000000000000000 : ℝ)*base67 + (2242384753211417361/587125000000000000000000000000000 : ℝ)*base69 + (200511785509542361/587125000000000000000000000000000 : ℝ)*base71 + (44238247192883/11742500000000000000000000000 : ℝ)*base73 + (836231926960167361/587125000000000000000000000000000 : ℝ)*base75 + (1749876119735082639/587125000000000000000000000000000 : ℝ)*base78 + (955657522803707639/587125000000000000000000000000000 : ℝ)*base80 + (6411148410221/1467812500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (3415999/2000000000000000000000 : ℝ)*base90 + (3415999/2000000000000000000000 : ℝ)*base92 + (3415999/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (14617/25000 : ℝ) ≤ (6865944932172461565882432851529/11742500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7639061/100000000000000 : ℝ)*(lower0) + (1893587/4000000000000 : ℝ)*(upper1) + (23506011/20000000000000 : ℝ)*(upper2) + (44932887436501/2000000000000 : ℝ)*(major0) + (44932887436501/2000000000000 : ℝ)*(major1) + (44932887436501/2000000000000 : ℝ)*(major2) + (1537741732842419/50000000000000 : ℝ)*(sp0) + (768870116452153/25000000000000 : ℝ)*(sp1) + (1537676835655189/50000000000000 : ℝ)*(sp2) + (1398303595724493/100000000000000 : ℝ)*(sp3) + (285441141/5000000000000 : ℝ)*(sp5) + (26500664211/20000000000000 : ℝ)*(sp10) + (4337357223/50000000000000 : ℝ)*(sp11) + (541789319/20000000000000 : ℝ)*(sp12) + (1398312270438939/100000000000000 : ℝ)*(f.failure) + (3075486174631433/100000000000000 : ℝ)*(f.sum) + (2300240041007/939400000000000000000000000 : ℝ)*base66 + (135206164887976157/46970000000000000000000000000000 : ℝ)*base68 + (130694570884136157/46970000000000000000000000000000 : ℝ)*base70 + (43053242576526157/46970000000000000000000000000000 : ℝ)*base72 + (52808699171/187880000000000000000000000 : ℝ)*base74 + (12280187103463843/46970000000000000000000000000000 : ℝ)*base75 + (245425113396106157/46970000000000000000000000000000 : ℝ)*base78 + (79614417023246157/46970000000000000000000000000000 : ℝ)*base80 + (6622341608731/4697000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (67227493/10000000000000000000000 : ℝ)*base89 + (67227493/10000000000000000000000 : ℝ)*base91 + (67227493/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (39973/50000 : ℝ) ≤ (29337170953882883226312155776389/36695312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (6076531/12500000000000 : ℝ)*(lower3) + (151509171/100000000000000 : ℝ)*(upper4) + (90663551/100000000000000 : ℝ)*(lower5) + (76386383659983/3125000000000 : ℝ)*(major0) + (76386383659983/3125000000000 : ℝ)*(major1) + (76386383659983/3125000000000 : ℝ)*(major2) + (571388201/12500000000000 : ℝ)*(sp0) + (1213273839/10000000000000 : ℝ)*(sp1) + (166325353153/100000000000000 : ℝ)*(sp2) + (78032763877/100000000000000 : ℝ)*(sp3) + (1670350718216961/50000000000000 : ℝ)*(sp8) + (167034693740057/5000000000000 : ℝ)*(sp9) + (1670269841093189/50000000000000 : ℝ)*(sp10) + (760647589158163/50000000000000 : ℝ)*(sp11) + (760686605540101/50000000000000 : ℝ)*(f.failure) + (334070600753953/10000000000000 : ℝ)*(f.sum) + (25929331666477/5871250000000000000000000000 : ℝ)*base66 + (18200842869939511/18347656250000000000000000000000 : ℝ)*base67 + (81656556446913057/9173828125000000000000000000000 : ℝ)*base70 + (351787898362163831/73390625000000000000000000000000 : ℝ)*base72 + (9293135766267/23485000000000000000000000000 : ℝ)*base73 + (29927037938279239/18347656250000000000000000000000 : ℝ)*base76 + (383187445521913831/73390625000000000000000000000000 : ℝ)*base78 + (130398215997935489/18347656250000000000000000000000 : ℝ)*base80 + (17435332210713/23485000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (62523013/5000000000000000000000 : ℝ)*base90 + (62523013/5000000000000000000000 : ℝ)*base92 + (62523013/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-4289/5000 : ℝ) ≤ (-125905900489473527848099090021833/146781250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (444801/12500000000000 : ℝ)*(lower0) + (910491/3125000000000 : ℝ)*(lower2) + (14145629/50000000000000 : ℝ)*(upper3) + (1293947/20000000000000 : ℝ)*(lower4) + (620653615919023/25000000000000 : ℝ)*(major0) + (620653615919023/25000000000000 : ℝ)*(major1) + (620653615919023/25000000000000 : ℝ)*(major2) + (438467389/25000000000000 : ℝ)*(sp0) + (42594939553/100000000000000 : ℝ)*(sp5) + (5912730371/12500000000000 : ℝ)*(sp6) + (862159917956311/25000000000000 : ℝ)*(sp12) + (215537426922203/6250000000000 : ℝ)*(sp13) + (3448594123851833/100000000000000 : ℝ)*(sp14) + (154518014104183/10000000000000 : ℝ)*(sp15) + (154518014104183/10000000000000 : ℝ)*(f.failure) + (3448641425694801/100000000000000 : ℝ)*(f.sum) + (8129740179657/2935625000000000000000000000 : ℝ)*base66 + (402395032417003111/587125000000000000000000000000000 : ℝ)*base68 + (2109010230661246889/587125000000000000000000000000000 : ℝ)*base69 + (6298375687385253111/587125000000000000000000000000000 : ℝ)*base72 + (15072995331087/11742500000000000000000000000 : ℝ)*base73 + (3125348779690378111/587125000000000000000000000000000 : ℝ)*base76 + (2494071666165628111/587125000000000000000000000000000 : ℝ)*base78 + (3127325830362128111/587125000000000000000000000000000 : ℝ)*base80 + (127542821766439/23485000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (2144521/1000000000000000000000 : ℝ)*base89 + (2144521/1000000000000000000000 : ℝ)*base91 + (2144521/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1478_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160668287/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (619/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5389/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(637/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(14617/25000 : ℝ) else (39973/50000 : ℝ) ≤ X j i ∧ X j i ≤ (4289/5000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1478_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1478_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160668287/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15477/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1347/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(637/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(14617/25000 : ℝ) else (39973/50000 : ℝ) ≤ X j i ∧ X j i ≤ (4289/5000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1478_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1478_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1478_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4451/1024 : ℝ) ≤ p) (hpb : p ≤ (4453/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160668287/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15477/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1347/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(637/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(14617/25000 : ℝ) else (39973/50000 : ℝ) ≤ X j i ∧ X j i ≤ (4289/5000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1478_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

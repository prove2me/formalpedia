-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1494_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:49:50.806012+00:00
-- url     : https://prove2.me/submissions/19093413-23fd-49fd-8c53-e11593aee2fe

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
theorem support_rectangle_w1494_s6_0 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-118433797/625000000 : ℝ)*x 0 + (5435585259/10000000000 : ℝ)*x 1 + (652084201/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (118433797/625000000 : ℝ)^4485 ≤ (5792007662351/50000000000000 : ℝ)^3461 := by
    have hnat : (118433797 : ℕ)^4485*50000000000000^3461 ≤ 5792007662351^3461*625000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118433797 625000000 5792007662351 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435585259/10000000000 : ℝ)^4485 ≤ (363081474017/800000000000 : ℝ)^3461 := by
    have hnat : (5435585259 : ℕ)^4485*800000000000^3461 ≤ 363081474017^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435585259 10000000000 363081474017 800000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (652084201/1250000000 : ℝ)^4485 ≤ (5378850050579/12500000000000 : ℝ)^3461 := by
    have hnat : (652084201 : ℕ)^4485*12500000000000^3461 ≤ 5378850050579^3461*1250000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652084201 1250000000 5378850050579 12500000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-118433797/625000000 : ℝ), (5435585259/10000000000 : ℝ), (652084201/1250000000 : ℝ)] ![(5792007662351/50000000000000 : ℝ), (363081474017/800000000000 : ℝ), (5378850050579/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-118433797/625000000 : ℝ)|^4485 ≤ (5792007662351/50000000000000 : ℝ)^3461
        have hw : |(-118433797/625000000 : ℝ)|=(118433797/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435585259/10000000000 : ℝ)|^4485 ≤ (363081474017/800000000000 : ℝ)^3461
        have hw : |(5435585259/10000000000 : ℝ)|=(5435585259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(652084201/1250000000 : ℝ)|^4485 ≤ (5378850050579/12500000000000 : ℝ)^3461
        have hw : |(652084201/1250000000 : ℝ)|=(652084201/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s6_1 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070514479/2000000000 : ℝ)*x 0 + (-2007098391/10000000000 : ℝ)*x 1 + (5216673607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070514479/2000000000 : ℝ)^4485 ≤ (556112735163/1250000000000 : ℝ)^3461 := by
    have hnat : (1070514479 : ℕ)^4485*1250000000000^3461 ≤ 556112735163^3461*2000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070514479 2000000000 556112735163 1250000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2007098391/10000000000 : ℝ)^4485 ≤ (3120045194333/25000000000000 : ℝ)^3461 := by
    have hnat : (2007098391 : ℕ)^4485*25000000000000^3461 ≤ 3120045194333^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2007098391 10000000000 3120045194333 25000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216673607/10000000000 : ℝ)^4485 ≤ (21515400196971/50000000000000 : ℝ)^3461 := by
    have hnat : (5216673607 : ℕ)^4485*50000000000000^3461 ≤ 21515400196971^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216673607 10000000000 21515400196971 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070514479/2000000000 : ℝ), (-2007098391/10000000000 : ℝ), (5216673607/10000000000 : ℝ)] ![(556112735163/1250000000000 : ℝ), (3120045194333/25000000000000 : ℝ), (21515400196971/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070514479/2000000000 : ℝ)|^4485 ≤ (556112735163/1250000000000 : ℝ)^3461
        have hw : |(1070514479/2000000000 : ℝ)|=(1070514479/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2007098391/10000000000 : ℝ)|^4485 ≤ (3120045194333/25000000000000 : ℝ)^3461
        have hw : |(-2007098391/10000000000 : ℝ)|=(2007098391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216673607/10000000000 : ℝ)|^4485 ≤ (21515400196971/50000000000000 : ℝ)^3461
        have hw : |(5216673607/10000000000 : ℝ)|=(5216673607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s6_2 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352572393/10000000000 : ℝ)*x 0 + (5216673607/10000000000 : ℝ)*x 1 + (-1003549197/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352572393/10000000000 : ℝ)^4485 ≤ (22244509395749/50000000000000 : ℝ)^3461 := by
    have hnat : (5352572393 : ℕ)^4485*50000000000000^3461 ≤ 22244509395749^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352572393 10000000000 22244509395749 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216673607/10000000000 : ℝ)^4485 ≤ (21515400196971/50000000000000 : ℝ)^3461 := by
    have hnat : (5216673607 : ℕ)^4485*50000000000000^3461 ≤ 21515400196971^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216673607 10000000000 21515400196971 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1003549197/5000000000 : ℝ)^4485 ≤ (2496036160301/20000000000000 : ℝ)^3461 := by
    have hnat : (1003549197 : ℕ)^4485*20000000000000^3461 ≤ 2496036160301^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003549197 5000000000 2496036160301 20000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352572393/10000000000 : ℝ), (5216673607/10000000000 : ℝ), (-1003549197/5000000000 : ℝ)] ![(22244509395749/50000000000000 : ℝ), (21515400196971/50000000000000 : ℝ), (2496036160301/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352572393/10000000000 : ℝ)|^4485 ≤ (22244509395749/50000000000000 : ℝ)^3461
        have hw : |(5352572393/10000000000 : ℝ)|=(5352572393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216673607/10000000000 : ℝ)|^4485 ≤ (21515400196971/50000000000000 : ℝ)^3461
        have hw : |(5216673607/10000000000 : ℝ)|=(5216673607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1003549197/5000000000 : ℝ)|^4485 ≤ (2496036160301/20000000000000 : ℝ)^3461
        have hw : |(-1003549197/5000000000 : ℝ)|=(1003549197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s6_3 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4278228929/10000000000 : ℝ)*x 0 + (4039222309/10000000000 : ℝ)*x 1 + (566166683/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4278228929/10000000000 : ℝ)^4485 ≤ (16639365314197/50000000000000 : ℝ)^3461 := by
    have hnat : (4278228929 : ℕ)^4485*50000000000000^3461 ≤ 16639365314197^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4278228929 10000000000 16639365314197 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4039222309/10000000000 : ℝ)^4485 ≤ (3861213153769/12500000000000 : ℝ)^3461 := by
    have hnat : (4039222309 : ℕ)^4485*12500000000000^3461 ≤ 3861213153769^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4039222309 10000000000 3861213153769 12500000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (566166683/1250000000 : ℝ)^4485 ≤ (17915782060591/50000000000000 : ℝ)^3461 := by
    have hnat : (566166683 : ℕ)^4485*50000000000000^3461 ≤ 17915782060591^3461*1250000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566166683 1250000000 17915782060591 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4278228929/10000000000 : ℝ), (4039222309/10000000000 : ℝ), (566166683/1250000000 : ℝ)] ![(16639365314197/50000000000000 : ℝ), (3861213153769/12500000000000 : ℝ), (17915782060591/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4278228929/10000000000 : ℝ)|^4485 ≤ (16639365314197/50000000000000 : ℝ)^3461
        have hw : |(4278228929/10000000000 : ℝ)|=(4278228929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4039222309/10000000000 : ℝ)|^4485 ≤ (3861213153769/12500000000000 : ℝ)^3461
        have hw : |(4039222309/10000000000 : ℝ)|=(4039222309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(566166683/1250000000 : ℝ)|^4485 ≤ (17915782060591/50000000000000 : ℝ)^3461
        have hw : |(566166683/1250000000 : ℝ)|=(566166683/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s6_4 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-947485449/5000000000 : ℝ)*x 0 + (5217796401/10000000000 : ℝ)*x 1 + (2717226949/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (947485449/5000000000 : ℝ)^4485 ≤ (11584254136101/100000000000000 : ℝ)^3461 := by
    have hnat : (947485449 : ℕ)^4485*100000000000000^3461 ≤ 11584254136101^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      947485449 5000000000 11584254136101 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217796401/10000000000 : ℝ)^4485 ≤ (43042802584497/100000000000000 : ℝ)^3461 := by
    have hnat : (5217796401 : ℕ)^4485*100000000000000^3461 ≤ 43042802584497^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217796401 10000000000 43042802584497 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2717226949/5000000000 : ℝ)^4485 ≤ (9074588652841/20000000000000 : ℝ)^3461 := by
    have hnat : (2717226949 : ℕ)^4485*20000000000000^3461 ≤ 9074588652841^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717226949 5000000000 9074588652841 20000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-947485449/5000000000 : ℝ), (5217796401/10000000000 : ℝ), (2717226949/5000000000 : ℝ)] ![(11584254136101/100000000000000 : ℝ), (43042802584497/100000000000000 : ℝ), (9074588652841/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-947485449/5000000000 : ℝ)|^4485 ≤ (11584254136101/100000000000000 : ℝ)^3461
        have hw : |(-947485449/5000000000 : ℝ)|=(947485449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217796401/10000000000 : ℝ)|^4485 ≤ (43042802584497/100000000000000 : ℝ)^3461
        have hw : |(5217796401/10000000000 : ℝ)|=(5217796401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2717226949/5000000000 : ℝ)|^4485 ≤ (9074588652841/20000000000000 : ℝ)^3461
        have hw : |(2717226949/5000000000 : ℝ)|=(2717226949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s6_5 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647633533/5000000000 : ℝ)*x 0 + (-894658967/5000000000 : ℝ)*x 1 + (2717227093/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647633533/5000000000 : ℝ)^4485 ≤ (43872770114241/100000000000000 : ℝ)^3461 := by
    have hnat : (2647633533 : ℕ)^4485*100000000000000^3461 ≤ 43872770114241^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647633533 5000000000 43872770114241 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (894658967/5000000000 : ℝ)^4485 ≤ (5377141743633/50000000000000 : ℝ)^3461 := by
    have hnat : (894658967 : ℕ)^4485*50000000000000^3461 ≤ 5377141743633^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894658967 5000000000 5377141743633 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2717227093/5000000000 : ℝ)^4485 ≤ (45372946380183/100000000000000 : ℝ)^3461 := by
    have hnat : (2717227093 : ℕ)^4485*100000000000000^3461 ≤ 45372946380183^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717227093 5000000000 45372946380183 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647633533/5000000000 : ℝ), (-894658967/5000000000 : ℝ), (2717227093/5000000000 : ℝ)] ![(43872770114241/100000000000000 : ℝ), (5377141743633/50000000000000 : ℝ), (45372946380183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647633533/5000000000 : ℝ)|^4485 ≤ (43872770114241/100000000000000 : ℝ)^3461
        have hw : |(2647633533/5000000000 : ℝ)|=(2647633533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-894658967/5000000000 : ℝ)|^4485 ≤ (5377141743633/50000000000000 : ℝ)^3461
        have hw : |(-894658967/5000000000 : ℝ)|=(894658967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2717227093/5000000000 : ℝ)|^4485 ≤ (45372946380183/100000000000000 : ℝ)^3461
        have hw : |(2717227093/5000000000 : ℝ)|=(2717227093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s6_6 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1059053487/2000000000 : ℝ)*x 0 + (1358613499/2500000000 : ℝ)*x 1 + (-178931769/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059053487/2000000000 : ℝ)^4485 ≤ (21936387038029/50000000000000 : ℝ)^3461 := by
    have hnat : (1059053487 : ℕ)^4485*50000000000000^3461 ≤ 21936387038029^3461*2000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059053487 2000000000 21936387038029 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358613499/2500000000 : ℝ)^4485 ≤ (45372944324503/100000000000000 : ℝ)^3461 := by
    have hnat : (1358613499 : ℕ)^4485*100000000000000^3461 ≤ 45372944324503^3461*2500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358613499 2500000000 45372944324503 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (178931769/1000000000 : ℝ)^4485 ≤ (10754281586867/100000000000000 : ℝ)^3461 := by
    have hnat : (178931769 : ℕ)^4485*100000000000000^3461 ≤ 10754281586867^3461*1000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      178931769 1000000000 10754281586867 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059053487/2000000000 : ℝ), (1358613499/2500000000 : ℝ), (-178931769/1000000000 : ℝ)] ![(21936387038029/50000000000000 : ℝ), (45372944324503/100000000000000 : ℝ), (10754281586867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059053487/2000000000 : ℝ)|^4485 ≤ (21936387038029/50000000000000 : ℝ)^3461
        have hw : |(1059053487/2000000000 : ℝ)|=(1059053487/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1358613499/2500000000 : ℝ)|^4485 ≤ (45372944324503/100000000000000 : ℝ)^3461
        have hw : |(1358613499/2500000000 : ℝ)|=(1358613499/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-178931769/1000000000 : ℝ)|^4485 ≤ (10754281586867/100000000000000 : ℝ)^3461
        have hw : |(-178931769/1000000000 : ℝ)|=(178931769/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s6_7 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534786987/1250000000 : ℝ)*x 0 + (4526819273/10000000000 : ℝ)*x 1 + (2020877293/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534786987/1250000000 : ℝ)^4485 ≤ (6655881132411/20000000000000 : ℝ)^3461 := by
    have hnat : (534786987 : ℕ)^4485*20000000000000^3461 ≤ 6655881132411^3461*1250000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534786987 1250000000 6655881132411 20000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4526819273/10000000000 : ℝ)^4485 ≤ (17902895858997/50000000000000 : ℝ)^3461 := by
    have hnat : (4526819273 : ℕ)^4485*50000000000000^3461 ≤ 17902895858997^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4526819273 10000000000 17902895858997 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2020877293/5000000000 : ℝ)^4485 ≤ (7728700651813/25000000000000 : ℝ)^3461 := by
    have hnat : (2020877293 : ℕ)^4485*25000000000000^3461 ≤ 7728700651813^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2020877293 5000000000 7728700651813 25000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534786987/1250000000 : ℝ), (4526819273/10000000000 : ℝ), (2020877293/5000000000 : ℝ)] ![(6655881132411/20000000000000 : ℝ), (17902895858997/50000000000000 : ℝ), (7728700651813/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534786987/1250000000 : ℝ)|^4485 ≤ (6655881132411/20000000000000 : ℝ)^3461
        have hw : |(534786987/1250000000 : ℝ)|=(534786987/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4526819273/10000000000 : ℝ)|^4485 ≤ (17902895858997/50000000000000 : ℝ)^3461
        have hw : |(4526819273/10000000000 : ℝ)|=(4526819273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2020877293/5000000000 : ℝ)|^4485 ≤ (7728700651813/25000000000000 : ℝ)^3461
        have hw : |(2020877293/5000000000 : ℝ)|=(2020877293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1494_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80971341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (387/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10843/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2711/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15479/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (387/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10843/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (387/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10843/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (387/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10843/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (387/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10843/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (387/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10843/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (387/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10843/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10843/100000 : ℝ) ^ (4483/1024 : ℝ) ≤ (2984847666305631/50000000000000000000 : ℝ) := by
    have hpowers : (10843/100000 : ℝ)^4483 ≤ (2984847666305631/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10843 : ℕ)^4483*50000000000000000000^1024 ≤ 2984847666305631^1024*100000^4483 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10843 100000 2984847666305631 50000000000000000000 4483 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10843/100000 : ℝ)) (X := (2984847666305631/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (387/2500 : ℝ) ^ (4483/1024 : ℝ) ≤ (28370972063748011/100000000000000000000 : ℝ) := by
    have hpowers : (387/2500 : ℝ)^4483 ≤ (28370972063748011/100000000000000000000 : ℝ)^1024 := by
      have hnat : (387 : ℕ)^4483*100000000000000000000^1024 ≤ 28370972063748011^1024*2500^4483 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        387 2500 28370972063748011 100000000000000000000 4483 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (387/2500 : ℝ)) (X := (28370972063748011/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002984847666305631/25000000000000000000 : ℝ) ≤ (2500068176293449/2500000000000000 : ℝ) ^ (4483/1024 : ℝ) := by
    have hpowers : (25002984847666305631/25000000000000000000 : ℝ)^1024 ≤ (2500068176293449/2500000000000000 : ℝ)^4483 := by
      have hnat : (25002984847666305631 : ℕ)^1024*2500000000000000^4483 ≤ 2500068176293449^4483*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002984847666305631 25000000000000000000 2500068176293449 2500000000000000 1024 4483 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500068176293449/2500000000000000 : ℝ)) (X := (25002984847666305631/25000000000000000000 : ℝ)) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100034340667396359273/100000000000000000000 : ℝ) ≤ (5000392150185257/5000000000000000 : ℝ) ^ (4483/1024 : ℝ) := by
    have hpowers : (100034340667396359273/100000000000000000000 : ℝ)^1024 ≤ (5000392150185257/5000000000000000 : ℝ)^4483 := by
      have hnat : (100034340667396359273 : ℕ)^1024*5000000000000000^4483 ≤ 5000392150185257^4483*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100034340667396359273 100000000000000000000 5000392150185257 5000000000000000 1024 4483 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000392150185257/5000000000000000 : ℝ)) (X := (100034340667396359273/100000000000000000000 : ℝ)) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028370972063748011/50000000000000000000 : ℝ) ≤ (78135124184119/78125000000000 : ℝ) ^ (4483/1024 : ℝ) := by
    have hpowers : (50028370972063748011/50000000000000000000 : ℝ)^1024 ≤ (78135124184119/78125000000000 : ℝ)^4483 := by
      have hnat : (50028370972063748011 : ℕ)^1024*78125000000000^4483 ≤ 78135124184119^4483*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028370972063748011 50000000000000000000 78135124184119 78125000000000 1024 4483 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78135124184119/78125000000000 : ℝ)) (X := (50028370972063748011/50000000000000000000 : ℝ)) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2984847666305631/50000000000000000000 : ℝ) ≤ ((1448755315014214547/1449062500000000000 : ℝ)+2*(255797598359/231850000000000 : ℝ)*(10843/100000 : ℝ))^(4483/1024 : ℝ) := by
    rw [show (1448755315014214547/1449062500000000000 : ℝ)+2*(255797598359/231850000000000 : ℝ)*(10843/100000 : ℝ)=(2500068176293449/2500000000000000 : ℝ) by norm_num, show 1+2*(2984847666305631/50000000000000000000 : ℝ)=(25002984847666305631/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28370972063748011/100000000000000000000 : ℝ)+(2984847666305631/50000000000000000000 : ℝ) ≤ ((1448755315014214547/1449062500000000000 : ℝ)+(255797598359/231850000000000 : ℝ)*((387/2500 : ℝ)+(10843/100000 : ℝ)))^(4483/1024 : ℝ) := by
    rw [show (1448755315014214547/1449062500000000000 : ℝ)+(255797598359/231850000000000 : ℝ)*((387/2500 : ℝ)+(10843/100000 : ℝ))=(5000392150185257/5000000000000000 : ℝ) by norm_num, show 1+(28370972063748011/100000000000000000000 : ℝ)+(2984847666305631/50000000000000000000 : ℝ)=(100034340667396359273/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28370972063748011/100000000000000000000 : ℝ) ≤ ((1448755315014214547/1449062500000000000 : ℝ)+2*(255797598359/231850000000000 : ℝ)*(387/2500 : ℝ))^(4483/1024 : ℝ) := by
    rw [show (1448755315014214547/1449062500000000000 : ℝ)+2*(255797598359/231850000000000 : ℝ)*(387/2500 : ℝ)=(78135124184119/78125000000000 : ℝ) by norm_num, show 1+2*(28370972063748011/100000000000000000000 : ℝ)=(50028370972063748011/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1448755315014214547/1449062500000000000 : ℝ)*(X 1 0+X 2 0)+(255797598359/231850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4483/1024 : ℝ)) (lo := (10843/100000 : ℝ)) (hi := (387/2500 : ℝ)) (c := (1448755315014214547/1449062500000000000 : ℝ)) (alpha := (255797598359/231850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1448755315014214547/1449062500000000000 : ℝ)*(X 0 1+X 2 1)+(255797598359/231850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4483/1024 : ℝ)) (lo := (10843/100000 : ℝ)) (hi := (387/2500 : ℝ)) (c := (1448755315014214547/1449062500000000000 : ℝ)) (alpha := (255797598359/231850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1448755315014214547/1449062500000000000 : ℝ)*(X 0 2+X 1 2)+(255797598359/231850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4483/1024 : ℝ)) (lo := (10843/100000 : ℝ)) (hi := (387/2500 : ℝ)) (c := (1448755315014214547/1449062500000000000 : ℝ)) (alpha := (255797598359/231850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-118433797/625000000 : ℝ)*X 0 0+(5435585259/10000000000 : ℝ)*X 0 1+(652084201/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070514479/2000000000 : ℝ)*X 1 0+(-2007098391/10000000000 : ℝ)*X 1 1+(5216673607/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352572393/10000000000 : ℝ)*X 2 0+(5216673607/10000000000 : ℝ)*X 2 1+(-1003549197/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4278228929/10000000000 : ℝ)*X 0 0+(4039222309/10000000000 : ℝ)*X 0 1+(566166683/1250000000 : ℝ)*X 0 2+(4278228929/10000000000 : ℝ)*X 1 0+(4039222309/10000000000 : ℝ)*X 1 1+(566166683/1250000000 : ℝ)*X 1 2+(4278228929/10000000000 : ℝ)*X 2 0+(4039222309/10000000000 : ℝ)*X 2 1+(566166683/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-947485449/5000000000 : ℝ)*X 0 0+(5217796401/10000000000 : ℝ)*X 0 1+(2717226949/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647633533/5000000000 : ℝ)*X 1 0+(-894658967/5000000000 : ℝ)*X 1 1+(2717227093/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1059053487/2000000000 : ℝ)*X 2 0+(1358613499/2500000000 : ℝ)*X 2 1+(-178931769/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((534786987/1250000000 : ℝ)*X 0 0+(4526819273/10000000000 : ℝ)*X 0 1+(2020877293/5000000000 : ℝ)*X 0 2+(534786987/1250000000 : ℝ)*X 1 0+(4526819273/10000000000 : ℝ)*X 1 1+(2020877293/5000000000 : ℝ)*X 1 2+(534786987/1250000000 : ℝ)*X 2 0+(4526819273/10000000000 : ℝ)*X 2 1+(2020877293/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (197285479111790293162556931/18113281250000000000000000000000 : ℝ) := by norm_num
    linear_combination (386530753/20000000000000 : ℝ)*(base19) + (1799825409/100000000000000 : ℝ)*(base23) + (17545929/25000000000000 : ℝ)*(lower2) + (34307849/12500000000000 : ℝ)*(upper3) + (175129487/100000000000000 : ℝ)*(upper5) + (3304247571567243/100000000000000 : ℝ)*(major0) + (3304247571567243/100000000000000 : ℝ)*(major1) + (3304247571567243/100000000000000 : ℝ)*(major2) + (913616808638467/20000000000000 : ℝ)*(sp0) + (2284055967816531/50000000000000 : ℝ)*(sp1) + (2284056034230709/50000000000000 : ℝ)*(sp2) + (204036639302699/10000000000000 : ℝ)*(sp3) + (7456273623/25000000000000 : ℝ)*(sp4) + (14518762061/100000000000000 : ℝ)*(sp7) + (2040380911789051/100000000000000 : ℝ)*(f.failure) + (4568113868286827/100000000000000 : ℝ)*(f.sum) + (16998612055769/5796250000000000000000000000 : ℝ)*base66 + (282967068998890171/144906250000000000000000000000000 : ℝ)*base67 + (107681950825952671/144906250000000000000000000000000 : ℝ)*base69 + (1270230125176015171/144906250000000000000000000000000 : ℝ)*base71 + (8294572636089/23185000000000000000000000000 : ℝ)*base73 + (43291543858609829/144906250000000000000000000000000 : ℝ)*base76 + (188952760538265171/144906250000000000000000000000000 : ℝ)*base77 + (122399109650358921/144906250000000000000000000000000 : ℝ)*base79 + (6368444802529/5796250000000000000000000000 : ℝ)*base82 + (18587391/5000000000000000000000 : ℝ)*base89 + (18587391/5000000000000000000000 : ℝ)*base91 + (18587391/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (598420376151615126621983523/72453125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (483212031/25000000000000 : ℝ)*(base19) + (122677211/5000000000000 : ℝ)*(base23) + (340199643/50000000000000 : ℝ)*(lower1) + (10953443/20000000000000 : ℝ)*(upper2) + (167489587/50000000000000 : ℝ)*(upper3) + (145262029/50000000000000 : ℝ)*(upper5) + (208659893803233/6250000000000 : ℝ)*(major0) + (208659893803233/6250000000000 : ℝ)*(major1) + (208659893803233/6250000000000 : ℝ)*(major2) + (8837215501/100000000000000 : ℝ)*(sp2) + (2307774227909699/50000000000000 : ℝ)*(sp4) + (4615546522971273/100000000000000 : ℝ)*(sp5) + (4615537165059677/100000000000000 : ℝ)*(sp6) + (515391967642559/25000000000000 : ℝ)*(sp7) + (515391967642559/25000000000000 : ℝ)*(f.failure) + (2307774227909699/50000000000000 : ℝ)*(f.sum) + (550822175771/5796250000000000000000000000 : ℝ)*base65 + (449965869670356321/36226562500000000000000000000000 : ℝ)*base68 + (387139634245532777/18113281250000000000000000000000 : ℝ)*base69 + (232823906501418821/36226562500000000000000000000000 : ℝ)*base72 + (922132495903/11592500000000000000000000000 : ℝ)*base74 + (358851692872018679/36226562500000000000000000000000 : ℝ)*base75 + (201779619011217223/18113281250000000000000000000000 : ℝ)*base78 + (486855810156915767/72453125000000000000000000000000 : ℝ)*base80 + (206708139994971/5796250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (10901619/1250000000000000000000 : ℝ)*base89 + (10901619/1250000000000000000000 : ℝ)*base91 + (10901619/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1494_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80971341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (387/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10843/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2711/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1494_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1494_s7_0 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1894941641/10000000000 : ℝ)*x 0 + (1358894763/2500000000 : ℝ)*x 1 + (81510613/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1894941641/10000000000 : ℝ)^4485 ≤ (1158402236719/10000000000000 : ℝ)^3461 := by
    have hnat : (1894941641 : ℕ)^4485*10000000000000^3461 ≤ 1158402236719^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1894941641 10000000000 1158402236719 10000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358894763/2500000000 : ℝ)^4485 ≤ (5673139636523/12500000000000 : ℝ)^3461 := by
    have hnat : (1358894763 : ℕ)^4485*12500000000000^3461 ≤ 5673139636523^3461*2500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358894763 2500000000 5673139636523 12500000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81510613/156250000 : ℝ)^4485 ≤ (672357195639/1562500000000 : ℝ)^3461 := by
    have hnat : (81510613 : ℕ)^4485*1562500000000^3461 ≤ 672357195639^3461*156250000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81510613 156250000 672357195639 1562500000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1894941641/10000000000 : ℝ), (1358894763/2500000000 : ℝ), (81510613/156250000 : ℝ)] ![(1158402236719/10000000000000 : ℝ), (5673139636523/12500000000000 : ℝ), (672357195639/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1894941641/10000000000 : ℝ)|^4485 ≤ (1158402236719/10000000000000 : ℝ)^3461
        have hw : |(-1894941641/10000000000 : ℝ)|=(1894941641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1358894763/2500000000 : ℝ)|^4485 ≤ (5673139636523/12500000000000 : ℝ)^3461
        have hw : |(1358894763/2500000000 : ℝ)|=(1358894763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81510613/156250000 : ℝ)|^4485 ≤ (672357195639/1562500000000 : ℝ)^3461
        have hw : |(81510613/156250000 : ℝ)|=(81510613/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s7_1 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676285431/5000000000 : ℝ)*x 0 + (-2007093079/10000000000 : ℝ)*x 1 + (1043335831/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676285431/5000000000 : ℝ)^4485 ≤ (11122250575321/25000000000000 : ℝ)^3461 := by
    have hnat : (2676285431 : ℕ)^4485*25000000000000^3461 ≤ 11122250575321^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676285431 5000000000 11122250575321 25000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2007093079/10000000000 : ℝ)^4485 ≤ (12480137974653/100000000000000 : ℝ)^3461 := by
    have hnat : (2007093079 : ℕ)^4485*100000000000000^3461 ≤ 12480137974653^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2007093079 10000000000 12480137974653 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043335831/2000000000 : ℝ)^4485 ≤ (1721234387913/4000000000000 : ℝ)^3461 := by
    have hnat : (1043335831 : ℕ)^4485*4000000000000^3461 ≤ 1721234387913^3461*2000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043335831 2000000000 1721234387913 4000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676285431/5000000000 : ℝ), (-2007093079/10000000000 : ℝ), (1043335831/2000000000 : ℝ)] ![(11122250575321/25000000000000 : ℝ), (12480137974653/100000000000000 : ℝ), (1721234387913/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676285431/5000000000 : ℝ)|^4485 ≤ (11122250575321/25000000000000 : ℝ)^3461
        have hw : |(2676285431/5000000000 : ℝ)|=(2676285431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2007093079/10000000000 : ℝ)|^4485 ≤ (12480137974653/100000000000000 : ℝ)^3461
        have hw : |(-2007093079/10000000000 : ℝ)|=(2007093079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043335831/2000000000 : ℝ)|^4485 ≤ (1721234387913/4000000000000 : ℝ)^3461
        have hw : |(1043335831/2000000000 : ℝ)|=(1043335831/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s7_2 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070514139/2000000000 : ℝ)*x 0 + (1304169931/2500000000 : ℝ)*x 1 + (-2007092549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070514139/2000000000 : ℝ)^4485 ≤ (11122250125637/25000000000000 : ℝ)^3461 := by
    have hnat : (1070514139 : ℕ)^4485*25000000000000^3461 ≤ 11122250125637^3461*2000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070514139 2000000000 11122250125637 25000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304169931/2500000000 : ℝ)^4485 ≤ (21515432890001/50000000000000 : ℝ)^3461 := by
    have hnat : (1304169931 : ℕ)^4485*50000000000000^3461 ≤ 21515432890001^3461*2500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304169931 2500000000 21515432890001 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2007092549/10000000000 : ℝ)^4485 ≤ (1560016713007/12500000000000 : ℝ)^3461 := by
    have hnat : (2007092549 : ℕ)^4485*12500000000000^3461 ≤ 1560016713007^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2007092549 10000000000 1560016713007 12500000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070514139/2000000000 : ℝ), (1304169931/2500000000 : ℝ), (-2007092549/10000000000 : ℝ)] ![(11122250125637/25000000000000 : ℝ), (21515432890001/50000000000000 : ℝ), (1560016713007/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070514139/2000000000 : ℝ)|^4485 ≤ (11122250125637/25000000000000 : ℝ)^3461
        have hw : |(1070514139/2000000000 : ℝ)|=(1070514139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304169931/2500000000 : ℝ)|^4485 ≤ (21515432890001/50000000000000 : ℝ)^3461
        have hw : |(1304169931/2500000000 : ℝ)|=(1304169931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2007092549/10000000000 : ℝ)|^4485 ≤ (1560016713007/12500000000000 : ℝ)^3461
        have hw : |(-2007092549/10000000000 : ℝ)|=(2007092549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s7_3 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069557477/2500000000 : ℝ)*x 0 + (2019617809/5000000000 : ℝ)*x 1 + (1132329909/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069557477/2500000000 : ℝ)^4485 ≤ (2079921281049/6250000000000 : ℝ)^3461 := by
    have hnat : (1069557477 : ℕ)^4485*6250000000000^3461 ≤ 2079921281049^3461*2500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069557477 2500000000 2079921281049 6250000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2019617809/5000000000 : ℝ)^4485 ≤ (15444918561689/50000000000000 : ℝ)^3461 := by
    have hnat : (2019617809 : ℕ)^4485*50000000000000^3461 ≤ 15444918561689^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2019617809 5000000000 15444918561689 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1132329909/2500000000 : ℝ)^4485 ≤ (2239463897619/6250000000000 : ℝ)^3461 := by
    have hnat : (1132329909 : ℕ)^4485*6250000000000^3461 ≤ 2239463897619^3461*2500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132329909 2500000000 2239463897619 6250000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069557477/2500000000 : ℝ), (2019617809/5000000000 : ℝ), (1132329909/2500000000 : ℝ)] ![(2079921281049/6250000000000 : ℝ), (15444918561689/50000000000000 : ℝ), (2239463897619/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069557477/2500000000 : ℝ)|^4485 ≤ (2079921281049/6250000000000 : ℝ)^3461
        have hw : |(1069557477/2500000000 : ℝ)|=(1069557477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2019617809/5000000000 : ℝ)|^4485 ≤ (15444918561689/50000000000000 : ℝ)^3461
        have hw : |(2019617809/5000000000 : ℝ)|=(2019617809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1132329909/2500000000 : ℝ)|^4485 ≤ (2239463897619/6250000000000 : ℝ)^3461
        have hw : |(1132329909/2500000000 : ℝ)|=(1132329909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s7_4 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-947485731/5000000000 : ℝ)*x 0 + (1304450511/2500000000 : ℝ)*x 1 + (543444791/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (947485731/5000000000 : ℝ)^4485 ≤ (5792129302011/50000000000000 : ℝ)^3461 := by
    have hnat : (947485731 : ℕ)^4485*50000000000000^3461 ≤ 5792129302011^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      947485731 5000000000 5792129302011 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304450511/2500000000 : ℝ)^4485 ≤ (21521431453849/50000000000000 : ℝ)^3461 := by
    have hnat : (1304450511 : ℕ)^4485*50000000000000^3461 ≤ 21521431453849^3461*2500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304450511 2500000000 21521431453849 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543444791/1000000000 : ℝ)^4485 ≤ (567160980973/1250000000000 : ℝ)^3461 := by
    have hnat : (543444791 : ℕ)^4485*1250000000000^3461 ≤ 567160980973^3461*1000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543444791 1000000000 567160980973 1250000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-947485731/5000000000 : ℝ), (1304450511/2500000000 : ℝ), (543444791/1000000000 : ℝ)] ![(5792129302011/50000000000000 : ℝ), (21521431453849/50000000000000 : ℝ), (567160980973/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-947485731/5000000000 : ℝ)|^4485 ≤ (5792129302011/50000000000000 : ℝ)^3461
        have hw : |(-947485731/5000000000 : ℝ)|=(947485731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304450511/2500000000 : ℝ)|^4485 ≤ (21521431453849/50000000000000 : ℝ)^3461
        have hw : |(1304450511/2500000000 : ℝ)|=(1304450511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(543444791/1000000000 : ℝ)|^4485 ≤ (567160980973/1250000000000 : ℝ)^3461
        have hw : |(543444791/1000000000 : ℝ)|=(543444791/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s7_5 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1059053761/2000000000 : ℝ)*x 0 + (-447331067/2500000000 : ℝ)*x 1 + (54344479/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059053761/2000000000 : ℝ)^4485 ≤ (10968197196311/25000000000000 : ℝ)^3461 := by
    have hnat : (1059053761 : ℕ)^4485*25000000000000^3461 ≤ 10968197196311^3461*2000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059053761 2000000000 10968197196311 25000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (447331067/2500000000 : ℝ)^4485 ≤ (10754332819763/100000000000000 : ℝ)^3461 := by
    have hnat : (447331067 : ℕ)^4485*100000000000000^3461 ≤ 10754332819763^3461*2500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447331067 2500000000 10754332819763 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54344479/100000000 : ℝ)^4485 ≤ (22686439184823/50000000000000 : ℝ)^3461 := by
    have hnat : (54344479 : ℕ)^4485*50000000000000^3461 ≤ 22686439184823^3461*100000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54344479 100000000 22686439184823 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059053761/2000000000 : ℝ), (-447331067/2500000000 : ℝ), (54344479/100000000 : ℝ)] ![(10968197196311/25000000000000 : ℝ), (10754332819763/100000000000000 : ℝ), (22686439184823/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059053761/2000000000 : ℝ)|^4485 ≤ (10968197196311/25000000000000 : ℝ)^3461
        have hw : |(1059053761/2000000000 : ℝ)|=(1059053761/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-447331067/2500000000 : ℝ)|^4485 ≤ (10754332819763/100000000000000 : ℝ)^3461
        have hw : |(-447331067/2500000000 : ℝ)|=(447331067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(54344479/100000000 : ℝ)|^4485 ≤ (22686439184823/50000000000000 : ℝ)^3461
        have hw : |(54344479/100000000 : ℝ)|=(54344479/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s7_6 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (34226369/80000000 : ℝ)*x 0 + (4526806119/10000000000 : ℝ)*x 1 + (1010441989/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34226369/80000000 : ℝ)^4485 ≤ (16639703985201/50000000000000 : ℝ)^3461 := by
    have hnat : (34226369 : ℕ)^4485*50000000000000^3461 ≤ 16639703985201^3461*80000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34226369 80000000 16639703985201 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4526806119/10000000000 : ℝ)^4485 ≤ (716113137809/2000000000000 : ℝ)^3461 := by
    have hnat : (4526806119 : ℕ)^4485*2000000000000^3461 ≤ 716113137809^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4526806119 10000000000 716113137809 2000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1010441989/2500000000 : ℝ)^4485 ≤ (6182987025913/20000000000000 : ℝ)^3461 := by
    have hnat : (1010441989 : ℕ)^4485*20000000000000^3461 ≤ 6182987025913^3461*2500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010441989 2500000000 6182987025913 20000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34226369/80000000 : ℝ), (4526806119/10000000000 : ℝ), (1010441989/2500000000 : ℝ)] ![(16639703985201/50000000000000 : ℝ), (716113137809/2000000000000 : ℝ), (6182987025913/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34226369/80000000 : ℝ)|^4485 ≤ (16639703985201/50000000000000 : ℝ)^3461
        have hw : |(34226369/80000000 : ℝ)|=(34226369/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4526806119/10000000000 : ℝ)|^4485 ≤ (716113137809/2000000000000 : ℝ)^3461
        have hw : |(4526806119/10000000000 : ℝ)|=(4526806119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1010441989/2500000000 : ℝ)|^4485 ≤ (6182987025913/20000000000000 : ℝ)^3461
        have hw : |(1010441989/2500000000 : ℝ)|=(1010441989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1494_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80971341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2711/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2169/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15479/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15479/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2711/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15479/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2711/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15479/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2711/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15479/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2711/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15479/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2711/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15479/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2711/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2711/25000 : ℝ) ^ (4483/1024 : ℝ) ≤ (5972106010249849/100000000000000000000 : ℝ) := by
    have hpowers : (2711/25000 : ℝ)^4483 ≤ (5972106010249849/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2711 : ℕ)^4483*100000000000000000000^1024 ≤ 5972106010249849^1024*25000^4483 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2711 25000 5972106010249849 100000000000000000000 4483 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2711/25000 : ℝ)) (X := (5972106010249849/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15479/100000 : ℝ) ^ (4483/1024 : ℝ) ≤ (1772684330494707/6250000000000000000 : ℝ) := by
    have hpowers : (15479/100000 : ℝ)^4483 ≤ (1772684330494707/6250000000000000000 : ℝ)^1024 := by
      have hnat : (15479 : ℕ)^4483*6250000000000000000^1024 ≤ 1772684330494707^1024*100000^4483 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15479 100000 1772684330494707 6250000000000000000 4483 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15479/100000 : ℝ)) (X := (1772684330494707/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005972106010249849/50000000000000000000 : ℝ) ≤ (10000272815292309/10000000000000000 : ℝ) ^ (4483/1024 : ℝ) := by
    have hpowers : (50005972106010249849/50000000000000000000 : ℝ)^1024 ≤ (10000272815292309/10000000000000000 : ℝ)^4483 := by
      have hnat : (50005972106010249849 : ℕ)^1024*10000000000000000^4483 ≤ 10000272815292309^4483*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005972106010249849 50000000000000000000 10000272815292309 10000000000000000 1024 4483 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000272815292309/10000000000000000 : ℝ)) (X := (50005972106010249849/50000000000000000000 : ℝ)) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100034335055298165161/100000000000000000000 : ℝ) ≤ (10000784172213779/10000000000000000 : ℝ) ^ (4483/1024 : ℝ) := by
    have hpowers : (100034335055298165161/100000000000000000000 : ℝ)^1024 ≤ (10000784172213779/10000000000000000 : ℝ)^4483 := by
      have hnat : (100034335055298165161 : ℕ)^1024*10000000000000000^4483 ≤ 10000784172213779^4483*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100034335055298165161 100000000000000000000 10000784172213779 10000000000000000 1024 4483 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000784172213779/10000000000000000 : ℝ)) (X := (100034335055298165161/100000000000000000000 : ℝ)) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3126772684330494707/3125000000000000000 : ℝ) ≤ (10001295529135249/10000000000000000 : ℝ) ^ (4483/1024 : ℝ) := by
    have hpowers : (3126772684330494707/3125000000000000000 : ℝ)^1024 ≤ (10001295529135249/10000000000000000 : ℝ)^4483 := by
      have hnat : (3126772684330494707 : ℕ)^1024*10000000000000000^4483 ≤ 10001295529135249^4483*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126772684330494707 3125000000000000000 10001295529135249 10000000000000000 1024 4483 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001295529135249/10000000000000000 : ℝ)) (X := (3126772684330494707/3125000000000000000 : ℝ)) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5972106010249849/100000000000000000000 : ℝ) ≤ ((9268034837993402171/9270000000000000000 : ℝ)+2*(51135692147/46350000000000 : ℝ)*(2711/25000 : ℝ))^(4483/1024 : ℝ) := by
    rw [show (9268034837993402171/9270000000000000000 : ℝ)+2*(51135692147/46350000000000 : ℝ)*(2711/25000 : ℝ)=(10000272815292309/10000000000000000 : ℝ) by norm_num, show 1+2*(5972106010249849/100000000000000000000 : ℝ)=(50005972106010249849/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1772684330494707/6250000000000000000 : ℝ)+(5972106010249849/100000000000000000000 : ℝ) ≤ ((9268034837993402171/9270000000000000000 : ℝ)+(51135692147/46350000000000 : ℝ)*((15479/100000 : ℝ)+(2711/25000 : ℝ)))^(4483/1024 : ℝ) := by
    rw [show (9268034837993402171/9270000000000000000 : ℝ)+(51135692147/46350000000000 : ℝ)*((15479/100000 : ℝ)+(2711/25000 : ℝ))=(10000784172213779/10000000000000000 : ℝ) by norm_num, show 1+(1772684330494707/6250000000000000000 : ℝ)+(5972106010249849/100000000000000000000 : ℝ)=(100034335055298165161/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1772684330494707/6250000000000000000 : ℝ) ≤ ((9268034837993402171/9270000000000000000 : ℝ)+2*(51135692147/46350000000000 : ℝ)*(15479/100000 : ℝ))^(4483/1024 : ℝ) := by
    rw [show (9268034837993402171/9270000000000000000 : ℝ)+2*(51135692147/46350000000000 : ℝ)*(15479/100000 : ℝ)=(10001295529135249/10000000000000000 : ℝ) by norm_num, show 1+2*(1772684330494707/6250000000000000000 : ℝ)=(3126772684330494707/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9268034837993402171/9270000000000000000 : ℝ)*(X 1 0+X 2 0)+(51135692147/46350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4483/1024 : ℝ)) (lo := (2711/25000 : ℝ)) (hi := (15479/100000 : ℝ)) (c := (9268034837993402171/9270000000000000000 : ℝ)) (alpha := (51135692147/46350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9268034837993402171/9270000000000000000 : ℝ)*(X 0 1+X 2 1)+(51135692147/46350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4483/1024 : ℝ)) (lo := (2711/25000 : ℝ)) (hi := (15479/100000 : ℝ)) (c := (9268034837993402171/9270000000000000000 : ℝ)) (alpha := (51135692147/46350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9268034837993402171/9270000000000000000 : ℝ)*(X 0 2+X 1 2)+(51135692147/46350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4483/1024 : ℝ)) (lo := (2711/25000 : ℝ)) (hi := (15479/100000 : ℝ)) (c := (9268034837993402171/9270000000000000000 : ℝ)) (alpha := (51135692147/46350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1894941641/10000000000 : ℝ)*X 0 0+(1358894763/2500000000 : ℝ)*X 0 1+(81510613/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676285431/5000000000 : ℝ)*X 1 0+(-2007093079/10000000000 : ℝ)*X 1 1+(1043335831/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070514139/2000000000 : ℝ)*X 2 0+(1304169931/2500000000 : ℝ)*X 2 1+(-2007092549/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1069557477/2500000000 : ℝ)*X 0 0+(2019617809/5000000000 : ℝ)*X 0 1+(1132329909/2500000000 : ℝ)*X 0 2+(1069557477/2500000000 : ℝ)*X 1 0+(2019617809/5000000000 : ℝ)*X 1 1+(1132329909/2500000000 : ℝ)*X 1 2+(1069557477/2500000000 : ℝ)*X 2 0+(2019617809/5000000000 : ℝ)*X 2 1+(1132329909/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-947485731/5000000000 : ℝ)*X 0 0+(1304450511/2500000000 : ℝ)*X 0 1+(543444791/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1059053761/2000000000 : ℝ)*X 1 0+(-447331067/2500000000 : ℝ)*X 1 1+(54344479/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((34226369/80000000 : ℝ)*X 0 0+(4526806119/10000000000 : ℝ)*X 0 1+(1010441989/2500000000 : ℝ)*X 0 2+(34226369/80000000 : ℝ)*X 1 0+(4526806119/10000000000 : ℝ)*X 1 1+(1010441989/2500000000 : ℝ)*X 1 2+(34226369/80000000 : ℝ)*X 2 0+(4526806119/10000000000 : ℝ)*X 2 1+(1010441989/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s7_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19015555227601043328711501/12875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (581895993/100000000000000 : ℝ)*(base19) + (49002749/12500000000000 : ℝ)*(base23) + (11104049/20000000000000 : ℝ)*(lower2) + (17718451/10000000000000 : ℝ)*(upper5) + (1652200707580693/50000000000000 : ℝ)*(major0) + (1652200707580693/50000000000000 : ℝ)*(major1) + (1652200707580693/50000000000000 : ℝ)*(major2) + (913662087513223/20000000000000 : ℝ)*(sp0) + (1142080255451239/25000000000000 : ℝ)*(sp1) + (2284163239243481/50000000000000 : ℝ)*(sp2) + (204047206058593/10000000000000 : ℝ)*(sp3) + (16432942839/100000000000000 : ℝ)*(sp4) + (1053361601/20000000000000 : ℝ)*(sp5) + (30078099/781250000000 : ℝ)*(sp6) + (2040475910582601/100000000000000 : ℝ)*(f.failure) + (2284163435254477/50000000000000 : ℝ)*(f.sum) + (36273230549461/4635000000000000000000000000 : ℝ)*base66 + (925551838401361501/154500000000000000000000000000000 : ℝ)*base67 + (685995556949638499/154500000000000000000000000000000 : ℝ)*base70 + (602884206247138499/154500000000000000000000000000000 : ℝ)*base72 + (103420642429/72421875000000000000000000 : ℝ)*base74 + (8650795244638499/154500000000000000000000000000000 : ℝ)*base76 + (1500096991415638499/154500000000000000000000000000000 : ℝ)*base78 + (1242913227062638499/154500000000000000000000000000000 : ℝ)*base80 + (7852900605503/2317500000000000000000000000 : ℝ)*base82 + (5762059/5000000000000000000000 : ℝ)*base90 + (5762059/5000000000000000000000 : ℝ)*base92 + (5762059/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1494_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80971341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2711/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2169/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1494_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1494_box_0 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-104877277/625000000 : ℝ)*x 0 + (5404781829/10000000000 : ℝ)*x 1 + (1351195481/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (104877277/625000000 : ℝ)^4485 ≤ (4947829612109/50000000000000 : ℝ)^3461 := by
    have hnat : (104877277 : ℕ)^4485*50000000000000^3461 ≤ 4947829612109^3461*625000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104877277 625000000 4947829612109 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5404781829/10000000000 : ℝ)^4485 ≤ (281576061681/625000000000 : ℝ)^3461 := by
    have hnat : (5404781829 : ℕ)^4485*625000000000^3461 ≤ 281576061681^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404781829 10000000000 281576061681 625000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351195481/2500000000 : ℝ)^4485 ≤ (1407880340473/3125000000000 : ℝ)^3461 := by
    have hnat : (1351195481 : ℕ)^4485*3125000000000^3461 ≤ 1407880340473^3461*2500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351195481 2500000000 1407880340473 3125000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-104877277/625000000 : ℝ), (5404781829/10000000000 : ℝ), (1351195481/2500000000 : ℝ)] ![(4947829612109/50000000000000 : ℝ), (281576061681/625000000000 : ℝ), (1407880340473/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-104877277/625000000 : ℝ)|^4485 ≤ (4947829612109/50000000000000 : ℝ)^3461
        have hw : |(-104877277/625000000 : ℝ)|=(104877277/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5404781829/10000000000 : ℝ)|^4485 ≤ (281576061681/625000000000 : ℝ)^3461
        have hw : |(5404781829/10000000000 : ℝ)|=(5404781829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351195481/2500000000 : ℝ)|^4485 ≤ (1407880340473/3125000000000 : ℝ)^3461
        have hw : |(1351195481/2500000000 : ℝ)|=(1351195481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_box_1 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1317626321/2500000000 : ℝ)*x 0 + (-233019577/1250000000 : ℝ)*x 1 + (2702390747/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1317626321/2500000000 : ℝ)^4485 ≤ (43607096107939/100000000000000 : ℝ)^3461 := by
    have hnat : (1317626321 : ℕ)^4485*100000000000000^3461 ≤ 43607096107939^3461*2500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317626321 2500000000 43607096107939 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (233019577/1250000000 : ℝ)^4485 ≤ (5670368809481/50000000000000 : ℝ)^3461 := by
    have hnat : (233019577 : ℕ)^4485*50000000000000^3461 ≤ 5670368809481^3461*1250000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233019577 1250000000 5670368809481 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2702390747/5000000000 : ℝ)^4485 ≤ (22526083125169/50000000000000 : ℝ)^3461 := by
    have hnat : (2702390747 : ℕ)^4485*50000000000000^3461 ≤ 22526083125169^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702390747 5000000000 22526083125169 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1317626321/2500000000 : ℝ), (-233019577/1250000000 : ℝ), (2702390747/5000000000 : ℝ)] ![(43607096107939/100000000000000 : ℝ), (5670368809481/50000000000000 : ℝ), (22526083125169/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1317626321/2500000000 : ℝ)|^4485 ≤ (43607096107939/100000000000000 : ℝ)^3461
        have hw : |(1317626321/2500000000 : ℝ)|=(1317626321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-233019577/1250000000 : ℝ)|^4485 ≤ (5670368809481/50000000000000 : ℝ)^3461
        have hw : |(-233019577/1250000000 : ℝ)|=(233019577/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2702390747/5000000000 : ℝ)|^4485 ≤ (22526083125169/50000000000000 : ℝ)^3461
        have hw : |(2702390747/5000000000 : ℝ)|=(2702390747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_box_2 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2635252207/5000000000 : ℝ)*x 0 + (5404782077/10000000000 : ℝ)*x 1 + (-932078501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2635252207/5000000000 : ℝ)^4485 ≤ (8721417356003/20000000000000 : ℝ)^3461 := by
    have hnat : (2635252207 : ℕ)^4485*20000000000000^3461 ≤ 8721417356003^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635252207 5000000000 8721417356003 20000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5404782077/10000000000 : ℝ)^4485 ≤ (2252608627391/5000000000000 : ℝ)^3461 := by
    have hnat : (5404782077 : ℕ)^4485*5000000000000^3461 ≤ 2252608627391^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404782077 10000000000 2252608627391 5000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (932078501/5000000000 : ℝ)^4485 ≤ (5670370330999/50000000000000 : ℝ)^3461 := by
    have hnat : (932078501 : ℕ)^4485*50000000000000^3461 ≤ 5670370330999^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      932078501 5000000000 5670370330999 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2635252207/5000000000 : ℝ), (5404782077/10000000000 : ℝ), (-932078501/5000000000 : ℝ)] ![(8721417356003/20000000000000 : ℝ), (2252608627391/5000000000000 : ℝ), (5670370330999/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2635252207/5000000000 : ℝ)|^4485 ≤ (8721417356003/20000000000000 : ℝ)^3461
        have hw : |(2635252207/5000000000 : ℝ)|=(2635252207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5404782077/10000000000 : ℝ)|^4485 ≤ (2252608627391/5000000000000 : ℝ)^3461
        have hw : |(5404782077/10000000000 : ℝ)|=(5404782077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-932078501/5000000000 : ℝ)|^4485 ≤ (5670370330999/50000000000000 : ℝ)^3461
        have hw : |(-932078501/5000000000 : ℝ)|=(932078501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_box_3 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4482135791/10000000000 : ℝ)*x 0 + (4183377803/10000000000 : ℝ)*x 1 + (4183376487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4482135791/10000000000 : ℝ)^4485 ≤ (8837114856137/25000000000000 : ℝ)^3461 := by
    have hnat : (4482135791 : ℕ)^4485*25000000000000^3461 ≤ 8837114856137^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4482135791 10000000000 8837114856137 25000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4183377803/10000000000 : ℝ)^4485 ≤ (6465155374843/20000000000000 : ℝ)^3461 := by
    have hnat : (4183377803 : ℕ)^4485*20000000000000^3461 ≤ 6465155374843^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4183377803 10000000000 6465155374843 20000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4183376487/10000000000 : ℝ)^4485 ≤ (16162881848273/50000000000000 : ℝ)^3461 := by
    have hnat : (4183376487 : ℕ)^4485*50000000000000^3461 ≤ 16162881848273^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4183376487 10000000000 16162881848273 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4482135791/10000000000 : ℝ), (4183377803/10000000000 : ℝ), (4183376487/10000000000 : ℝ)] ![(8837114856137/25000000000000 : ℝ), (6465155374843/20000000000000 : ℝ), (16162881848273/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4482135791/10000000000 : ℝ)|^4485 ≤ (8837114856137/25000000000000 : ℝ)^3461
        have hw : |(4482135791/10000000000 : ℝ)|=(4482135791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4183377803/10000000000 : ℝ)|^4485 ≤ (6465155374843/20000000000000 : ℝ)^3461
        have hw : |(4183377803/10000000000 : ℝ)|=(4183377803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4183376487/10000000000 : ℝ)|^4485 ≤ (16162881848273/50000000000000 : ℝ)^3461
        have hw : |(4183376487/10000000000 : ℝ)|=(4183376487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_box_4 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-529324071/2500000000 : ℝ)*x 0 + (2621497847/5000000000 : ℝ)*x 1 + (2621498133/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529324071/2500000000 : ℝ)^4485 ≤ (1337524759557/10000000000000 : ℝ)^3461 := by
    have hnat : (529324071 : ℕ)^4485*10000000000000^3461 ≤ 1337524759557^3461*2500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529324071 2500000000 1337524759557 10000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621497847/5000000000 : ℝ)^4485 ≤ (1732494925143/4000000000000 : ℝ)^3461 := by
    have hnat : (2621497847 : ℕ)^4485*4000000000000^3461 ≤ 1732494925143^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621497847 5000000000 1732494925143 4000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621498133/5000000000 : ℝ)^4485 ≤ (43312379251929/100000000000000 : ℝ)^3461 := by
    have hnat : (2621498133 : ℕ)^4485*100000000000000^3461 ≤ 43312379251929^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621498133 5000000000 43312379251929 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-529324071/2500000000 : ℝ), (2621497847/5000000000 : ℝ), (2621498133/5000000000 : ℝ)] ![(1337524759557/10000000000000 : ℝ), (1732494925143/4000000000000 : ℝ), (43312379251929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-529324071/2500000000 : ℝ)|^4485 ≤ (1337524759557/10000000000000 : ℝ)^3461
        have hw : |(-529324071/2500000000 : ℝ)|=(529324071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621497847/5000000000 : ℝ)|^4485 ≤ (1732494925143/4000000000000 : ℝ)^3461
        have hw : |(2621497847/5000000000 : ℝ)|=(2621497847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621498133/5000000000 : ℝ)|^4485 ≤ (43312379251929/100000000000000 : ℝ)^3461
        have hw : |(2621498133/5000000000 : ℝ)|=(2621498133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_box_5 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1345825399/2500000000 : ℝ)*x 0 + (-386121529/2000000000 : ℝ)*x 1 + (2621497937/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345825399/2500000000 : ℝ)^4485 ≤ (44820280023837/100000000000000 : ℝ)^3461 := by
    have hnat : (1345825399 : ℕ)^4485*100000000000000^3461 ≤ 44820280023837^3461*2500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345825399 2500000000 44820280023837 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (386121529/2000000000 : ℝ)^4485 ≤ (5933672451883/50000000000000 : ℝ)^3461 := by
    have hnat : (386121529 : ℕ)^4485*50000000000000^3461 ≤ 5933672451883^3461*2000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      386121529 2000000000 5933672451883 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621497937/5000000000 : ℝ)^4485 ≤ (8662475011101/20000000000000 : ℝ)^3461 := by
    have hnat : (2621497937 : ℕ)^4485*20000000000000^3461 ≤ 8662475011101^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621497937 5000000000 8662475011101 20000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1345825399/2500000000 : ℝ), (-386121529/2000000000 : ℝ), (2621497937/5000000000 : ℝ)] ![(44820280023837/100000000000000 : ℝ), (5933672451883/50000000000000 : ℝ), (8662475011101/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1345825399/2500000000 : ℝ)|^4485 ≤ (44820280023837/100000000000000 : ℝ)^3461
        have hw : |(1345825399/2500000000 : ℝ)|=(1345825399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-386121529/2000000000 : ℝ)|^4485 ≤ (5933672451883/50000000000000 : ℝ)^3461
        have hw : |(-386121529/2000000000 : ℝ)|=(386121529/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621497937/5000000000 : ℝ)|^4485 ≤ (8662475011101/20000000000000 : ℝ)^3461
        have hw : |(2621497937/5000000000 : ℝ)|=(2621497937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_box_6 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (336456313/625000000 : ℝ)*x 0 + (41943971/80000000 : ℝ)*x 1 + (-1930607769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (336456313/625000000 : ℝ)^4485 ≤ (1792810947193/4000000000000 : ℝ)^3461 := by
    have hnat : (336456313 : ℕ)^4485*4000000000000^3461 ≤ 1792810947193^3461*625000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336456313 625000000 1792810947193 4000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41943971/80000000 : ℝ)^4485 ≤ (5414047552349/12500000000000 : ℝ)^3461 := by
    have hnat : (41943971 : ℕ)^4485*12500000000000^3461 ≤ 5414047552349^3461*80000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41943971 80000000 5414047552349 12500000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1930607769/10000000000 : ℝ)^4485 ≤ (2373469178301/20000000000000 : ℝ)^3461 := by
    have hnat : (1930607769 : ℕ)^4485*20000000000000^3461 ≤ 2373469178301^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1930607769 10000000000 2373469178301 20000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(336456313/625000000 : ℝ), (41943971/80000000 : ℝ), (-1930607769/10000000000 : ℝ)] ![(1792810947193/4000000000000 : ℝ), (5414047552349/12500000000000 : ℝ), (2373469178301/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(336456313/625000000 : ℝ)|^4485 ≤ (1792810947193/4000000000000 : ℝ)^3461
        have hw : |(336456313/625000000 : ℝ)|=(336456313/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41943971/80000000 : ℝ)|^4485 ≤ (5414047552349/12500000000000 : ℝ)^3461
        have hw : |(41943971/80000000 : ℝ)|=(41943971/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1930607769/10000000000 : ℝ)|^4485 ≤ (2373469178301/20000000000000 : ℝ)^3461
        have hw : |(-1930607769/10000000000 : ℝ)|=(1930607769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_box_7 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (814398499/2000000000 : ℝ)*x 0 + (4388312267/10000000000 : ℝ)*x 1 + (438831193/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (814398499/2000000000 : ℝ)^4485 ≤ (31214849194769/100000000000000 : ℝ)^3461 := by
    have hnat : (814398499 : ℕ)^4485*100000000000000^3461 ≤ 31214849194769^3461*2000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      814398499 2000000000 31214849194769 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4388312267/10000000000 : ℝ)^4485 ≤ (6878515421149/20000000000000 : ℝ)^3461 := by
    have hnat : (4388312267 : ℕ)^4485*20000000000000^3461 ≤ 6878515421149^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4388312267 10000000000 6878515421149 20000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (438831193/1000000000 : ℝ)^4485 ≤ (34392573683131/100000000000000 : ℝ)^3461 := by
    have hnat : (438831193 : ℕ)^4485*100000000000000^3461 ≤ 34392573683131^3461*1000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438831193 1000000000 34392573683131 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(814398499/2000000000 : ℝ), (4388312267/10000000000 : ℝ), (438831193/1000000000 : ℝ)] ![(31214849194769/100000000000000 : ℝ), (6878515421149/20000000000000 : ℝ), (34392573683131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(814398499/2000000000 : ℝ)|^4485 ≤ (31214849194769/100000000000000 : ℝ)^3461
        have hw : |(814398499/2000000000 : ℝ)|=(814398499/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4388312267/10000000000 : ℝ)|^4485 ≤ (6878515421149/20000000000000 : ℝ)^3461
        have hw : |(4388312267/10000000000 : ℝ)|=(4388312267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(438831193/1000000000 : ℝ)|^4485 ≤ (34392573683131/100000000000000 : ℝ)^3461
        have hw : |(438831193/1000000000 : ℝ)|=(438831193/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_box_8 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2024569891/10000000000 : ℝ)*x 0 + (1282463587/2500000000 : ℝ)*x 1 + (5425287627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2024569891/10000000000 : ℝ)^4485 ≤ (12621142441369/100000000000000 : ℝ)^3461 := by
    have hnat : (2024569891 : ℕ)^4485*100000000000000^3461 ≤ 12621142441369^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2024569891 10000000000 12621142441369 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1282463587/2500000000 : ℝ)^4485 ≤ (42105062786227/100000000000000 : ℝ)^3461 := by
    have hnat : (1282463587 : ℕ)^4485*100000000000000^3461 ≤ 42105062786227^3461*2500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1282463587 2500000000 42105062786227 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5425287627/10000000000 : ℝ)^4485 ≤ (11318448690223/25000000000000 : ℝ)^3461 := by
    have hnat : (5425287627 : ℕ)^4485*25000000000000^3461 ≤ 11318448690223^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425287627 10000000000 11318448690223 25000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2024569891/10000000000 : ℝ), (1282463587/2500000000 : ℝ), (5425287627/10000000000 : ℝ)] ![(12621142441369/100000000000000 : ℝ), (42105062786227/100000000000000 : ℝ), (11318448690223/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2024569891/10000000000 : ℝ)|^4485 ≤ (12621142441369/100000000000000 : ℝ)^3461
        have hw : |(-2024569891/10000000000 : ℝ)|=(2024569891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1282463587/2500000000 : ℝ)|^4485 ≤ (42105062786227/100000000000000 : ℝ)^3461
        have hw : |(1282463587/2500000000 : ℝ)|=(1282463587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5425287627/10000000000 : ℝ)|^4485 ≤ (11318448690223/25000000000000 : ℝ)^3461
        have hw : |(5425287627/10000000000 : ℝ)|=(5425287627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_box_9 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256201521/10000000000 : ℝ)*x 0 + (-231935471/1250000000 : ℝ)*x 1 + (135632183/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256201521/10000000000 : ℝ)^4485 ≤ (10863449079489/25000000000000 : ℝ)^3461 := by
    have hnat : (5256201521 : ℕ)^4485*25000000000000^3461 ≤ 10863449079489^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256201521 10000000000 10863449079489 25000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (231935471/1250000000 : ℝ)^4485 ≤ (11272412223371/100000000000000 : ℝ)^3461 := by
    have hnat : (231935471 : ℕ)^4485*100000000000000^3461 ≤ 11272412223371^3461*1250000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231935471 1250000000 11272412223371 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135632183/250000000 : ℝ)^4485 ≤ (11318447860251/25000000000000 : ℝ)^3461 := by
    have hnat : (135632183 : ℕ)^4485*25000000000000^3461 ≤ 11318447860251^3461*250000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135632183 250000000 11318447860251 25000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256201521/10000000000 : ℝ), (-231935471/1250000000 : ℝ), (135632183/250000000 : ℝ)] ![(10863449079489/25000000000000 : ℝ), (11272412223371/100000000000000 : ℝ), (11318447860251/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256201521/10000000000 : ℝ)|^4485 ≤ (10863449079489/25000000000000 : ℝ)^3461
        have hw : |(5256201521/10000000000 : ℝ)|=(5256201521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-231935471/1250000000 : ℝ)|^4485 ≤ (11272412223371/100000000000000 : ℝ)^3461
        have hw : |(-231935471/1250000000 : ℝ)|=(231935471/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135632183/250000000 : ℝ)|^4485 ≤ (11318447860251/25000000000000 : ℝ)^3461
        have hw : |(135632183/250000000 : ℝ)|=(135632183/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_box_10 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314050201/2500000000 : ℝ)*x 0 + (5425288261/10000000000 : ℝ)*x 1 + (-463870863/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314050201/2500000000 : ℝ)^4485 ≤ (43453788636639/100000000000000 : ℝ)^3461 := by
    have hnat : (1314050201 : ℕ)^4485*100000000000000^3461 ≤ 43453788636639^3461*2500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314050201 2500000000 43453788636639 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5425288261/10000000000 : ℝ)^4485 ≤ (22636900808473/50000000000000 : ℝ)^3461 := by
    have hnat : (5425288261 : ℕ)^4485*50000000000000^3461 ≤ 22636900808473^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425288261 10000000000 22636900808473 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (463870863/2500000000 : ℝ)^4485 ≤ (176131402119/1562500000000 : ℝ)^3461 := by
    have hnat : (463870863 : ℕ)^4485*1562500000000^3461 ≤ 176131402119^3461*2500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      463870863 2500000000 176131402119 1562500000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314050201/2500000000 : ℝ), (5425288261/10000000000 : ℝ), (-463870863/2500000000 : ℝ)] ![(43453788636639/100000000000000 : ℝ), (22636900808473/50000000000000 : ℝ), (176131402119/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314050201/2500000000 : ℝ)|^4485 ≤ (43453788636639/100000000000000 : ℝ)^3461
        have hw : |(1314050201/2500000000 : ℝ)|=(1314050201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5425288261/10000000000 : ℝ)|^4485 ≤ (22636900808473/50000000000000 : ℝ)^3461
        have hw : |(5425288261/10000000000 : ℝ)|=(5425288261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-463870863/2500000000 : ℝ)|^4485 ≤ (176131402119/1562500000000 : ℝ)^3461
        have hw : |(-463870863/2500000000 : ℝ)|=(463870863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_box_11 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (566620797/1250000000 : ℝ)*x 0 + (2078685349/5000000000 : ℝ)*x 1 + (259835639/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (566620797/1250000000 : ℝ)^4485 ≤ (17934405878627/50000000000000 : ℝ)^3461 := by
    have hnat : (566620797 : ℕ)^4485*50000000000000^3461 ≤ 17934405878627^3461*1250000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566620797 1250000000 17934405878627 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2078685349/5000000000 : ℝ)^4485 ≤ (32065596481453/100000000000000 : ℝ)^3461 := by
    have hnat : (2078685349 : ℕ)^4485*100000000000000^3461 ≤ 32065596481453^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078685349 5000000000 32065596481453 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (259835639/625000000 : ℝ)^4485 ≤ (16032795871919/50000000000000 : ℝ)^3461 := by
    have hnat : (259835639 : ℕ)^4485*50000000000000^3461 ≤ 16032795871919^3461*625000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259835639 625000000 16032795871919 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(566620797/1250000000 : ℝ), (2078685349/5000000000 : ℝ), (259835639/625000000 : ℝ)] ![(17934405878627/50000000000000 : ℝ), (32065596481453/100000000000000 : ℝ), (16032795871919/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(566620797/1250000000 : ℝ)|^4485 ≤ (17934405878627/50000000000000 : ℝ)^3461
        have hw : |(566620797/1250000000 : ℝ)|=(566620797/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2078685349/5000000000 : ℝ)|^4485 ≤ (32065596481453/100000000000000 : ℝ)^3461
        have hw : |(2078685349/5000000000 : ℝ)|=(2078685349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(259835639/625000000 : ℝ)|^4485 ≤ (16032795871919/50000000000000 : ℝ)^3461
        have hw : |(259835639/625000000 : ℝ)|=(259835639/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_box_12 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1770812403/10000000000 : ℝ)*x 0 + (2757111387/5000000000 : ℝ)*x 1 + (5227986597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1770812403/10000000000 : ℝ)^4485 ≤ (1326296735457/12500000000000 : ℝ)^3461 := by
    have hnat : (1770812403 : ℕ)^4485*12500000000000^3461 ≤ 1326296735457^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1770812403 10000000000 1326296735457 12500000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2757111387/5000000000 : ℝ)^4485 ≤ (9247571943989/20000000000000 : ℝ)^3461 := by
    have hnat : (2757111387 : ℕ)^4485*20000000000000^3461 ≤ 9247571943989^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757111387 5000000000 9247571943989 20000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5227986597/10000000000 : ℝ)^4485 ≤ (8630353274599/20000000000000 : ℝ)^3461 := by
    have hnat : (5227986597 : ℕ)^4485*20000000000000^3461 ≤ 8630353274599^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227986597 10000000000 8630353274599 20000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1770812403/10000000000 : ℝ), (2757111387/5000000000 : ℝ), (5227986597/10000000000 : ℝ)] ![(1326296735457/12500000000000 : ℝ), (9247571943989/20000000000000 : ℝ), (8630353274599/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1770812403/10000000000 : ℝ)|^4485 ≤ (1326296735457/12500000000000 : ℝ)^3461
        have hw : |(-1770812403/10000000000 : ℝ)|=(1770812403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2757111387/5000000000 : ℝ)|^4485 ≤ (9247571943989/20000000000000 : ℝ)^3461
        have hw : |(2757111387/5000000000 : ℝ)|=(2757111387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5227986597/10000000000 : ℝ)|^4485 ≤ (8630353274599/20000000000000 : ℝ)^3461
        have hw : |(5227986597/10000000000 : ℝ)|=(5227986597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_box_13 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2696882741/5000000000 : ℝ)*x 0 + (-968295737/5000000000 : ℝ)*x 1 + (163374561/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2696882741/5000000000 : ℝ)^4485 ≤ (11233302192609/25000000000000 : ℝ)^3461 := by
    have hnat : (2696882741 : ℕ)^4485*25000000000000^3461 ≤ 11233302192609^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696882741 5000000000 11233302192609 25000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (968295737/5000000000 : ℝ)^4485 ≤ (476601269579/4000000000000 : ℝ)^3461 := by
    have hnat : (968295737 : ℕ)^4485*4000000000000^3461 ≤ 476601269579^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      968295737 5000000000 476601269579 4000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163374561/312500000 : ℝ)^4485 ≤ (21575879737009/50000000000000 : ℝ)^3461 := by
    have hnat : (163374561 : ℕ)^4485*50000000000000^3461 ≤ 21575879737009^3461*312500000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163374561 312500000 21575879737009 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2696882741/5000000000 : ℝ), (-968295737/5000000000 : ℝ), (163374561/312500000 : ℝ)] ![(11233302192609/25000000000000 : ℝ), (476601269579/4000000000000 : ℝ), (21575879737009/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2696882741/5000000000 : ℝ)|^4485 ≤ (11233302192609/25000000000000 : ℝ)^3461
        have hw : |(2696882741/5000000000 : ℝ)|=(2696882741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-968295737/5000000000 : ℝ)|^4485 ≤ (476601269579/4000000000000 : ℝ)^3461
        have hw : |(-968295737/5000000000 : ℝ)|=(968295737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163374561/312500000 : ℝ)|^4485 ≤ (21575879737009/50000000000000 : ℝ)^3461
        have hw : |(163374561/312500000 : ℝ)|=(163374561/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_box_14 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5393765133/10000000000 : ℝ)*x 0 + (1045597299/2000000000 : ℝ)*x 1 + (-1936591219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5393765133/10000000000 : ℝ)^4485 ≤ (2808325312679/6250000000000 : ℝ)^3461 := by
    have hnat : (5393765133 : ℕ)^4485*6250000000000^3461 ≤ 2808325312679^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393765133 10000000000 2808325312679 6250000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1045597299/2000000000 : ℝ)^4485 ≤ (21575882640997/50000000000000 : ℝ)^3461 := by
    have hnat : (1045597299 : ℕ)^4485*50000000000000^3461 ≤ 21575882640997^3461*2000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045597299 2000000000 21575882640997 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1936591219/10000000000 : ℝ)^4485 ≤ (5957514853189/50000000000000 : ℝ)^3461 := by
    have hnat : (1936591219 : ℕ)^4485*50000000000000^3461 ≤ 5957514853189^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1936591219 10000000000 5957514853189 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5393765133/10000000000 : ℝ), (1045597299/2000000000 : ℝ), (-1936591219/10000000000 : ℝ)] ![(2808325312679/6250000000000 : ℝ), (21575882640997/50000000000000 : ℝ), (5957514853189/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5393765133/10000000000 : ℝ)|^4485 ≤ (2808325312679/6250000000000 : ℝ)^3461
        have hw : |(5393765133/10000000000 : ℝ)|=(5393765133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1045597299/2000000000 : ℝ)|^4485 ≤ (21575882640997/50000000000000 : ℝ)^3461
        have hw : |(1045597299/2000000000 : ℝ)|=(1045597299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1936591219/10000000000 : ℝ)|^4485 ≤ (5957514853189/50000000000000 : ℝ)^3461
        have hw : |(-1936591219/10000000000 : ℝ)|=(1936591219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_box_15 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4033081887/10000000000 : ℝ)*x 0 + (2203651519/5000000000 : ℝ)*x 1 + (1101825437/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4033081887/10000000000 : ℝ)^4485 ≤ (30828866889441/100000000000000 : ℝ)^3461 := by
    have hnat : (4033081887 : ℕ)^4485*100000000000000^3461 ≤ 30828866889441^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4033081887 10000000000 30828866889441 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2203651519/5000000000 : ℝ)^4485 ≤ (34585573103937/100000000000000 : ℝ)^3461 := by
    have hnat : (2203651519 : ℕ)^4485*100000000000000^3461 ≤ 34585573103937^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203651519 5000000000 34585573103937 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1101825437/2500000000 : ℝ)^4485 ≤ (34585559985787/100000000000000 : ℝ)^3461 := by
    have hnat : (1101825437 : ℕ)^4485*100000000000000^3461 ≤ 34585559985787^3461*2500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101825437 2500000000 34585559985787 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4033081887/10000000000 : ℝ), (2203651519/5000000000 : ℝ), (1101825437/2500000000 : ℝ)] ![(30828866889441/100000000000000 : ℝ), (34585573103937/100000000000000 : ℝ), (34585559985787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4033081887/10000000000 : ℝ)|^4485 ≤ (30828866889441/100000000000000 : ℝ)^3461
        have hw : |(4033081887/10000000000 : ℝ)|=(4033081887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2203651519/5000000000 : ℝ)|^4485 ≤ (34585573103937/100000000000000 : ℝ)^3461
        have hw : |(2203651519/5000000000 : ℝ)|=(2203651519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1101825437/2500000000 : ℝ)|^4485 ≤ (34585559985787/100000000000000 : ℝ)^3461
        have hw : |(1101825437/2500000000 : ℝ)|=(1101825437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1494_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80971341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2169/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(63717/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58543/100000 : ℝ) ∧ (20031/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (17177/20000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15479/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2169/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15479/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2169/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15479/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2169/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15479/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2169/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15479/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2169/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15479/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2169/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2169/20000 : ℝ) ^ (4483/1024 : ℝ) ≤ (1493629359734189/25000000000000000000 : ℝ) := by
    have hpowers : (2169/20000 : ℝ)^4483 ≤ (1493629359734189/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2169 : ℕ)^4483*25000000000000000000^1024 ≤ 1493629359734189^1024*20000^4483 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2169 20000 1493629359734189 25000000000000000000 4483 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2169/20000 : ℝ)) (X := (1493629359734189/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15479/100000 : ℝ) ^ (4483/1024 : ℝ) ≤ (1772684330494707/6250000000000000000 : ℝ) := by
    have hpowers : (15479/100000 : ℝ)^4483 ≤ (1772684330494707/6250000000000000000 : ℝ)^1024 := by
      have hnat : (15479 : ℕ)^4483*6250000000000000000^1024 ≤ 1772684330494707^1024*100000^4483 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15479 100000 1772684330494707 6250000000000000000 4483 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15479/100000 : ℝ)) (X := (1772684330494707/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501493629359734189/12500000000000000000 : ℝ) ≤ (80002183403561/80000000000000 : ℝ) ^ (4483/1024 : ℝ) := by
    have hpowers : (12501493629359734189/12500000000000000000 : ℝ)^1024 ≤ (80002183403561/80000000000000 : ℝ)^4483 := by
      have hnat : (12501493629359734189 : ℕ)^1024*80000000000000^4483 ≤ 80002183403561^4483*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501493629359734189 12500000000000000000 80002183403561 80000000000000 1024 4483 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80002183403561/80000000000000 : ℝ)) (X := (12501493629359734189/12500000000000000000 : ℝ)) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25008584366681713017/25000000000000000000 : ℝ) ≤ (400031369091227/400000000000000 : ℝ) ^ (4483/1024 : ℝ) := by
    have hpowers : (25008584366681713017/25000000000000000000 : ℝ)^1024 ≤ (400031369091227/400000000000000 : ℝ)^4483 := by
      have hnat : (25008584366681713017 : ℕ)^1024*400000000000000^4483 ≤ 400031369091227^4483*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008584366681713017 25000000000000000000 400031369091227 400000000000000 1024 4483 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400031369091227/400000000000000 : ℝ)) (X := (25008584366681713017/25000000000000000000 : ℝ)) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3126772684330494707/3125000000000000000 : ℝ) ≤ (400051821164649/400000000000000 : ℝ) ^ (4483/1024 : ℝ) := by
    have hpowers : (3126772684330494707/3125000000000000000 : ℝ)^1024 ≤ (400051821164649/400000000000000 : ℝ)^4483 := by
      have hnat : (3126772684330494707 : ℕ)^1024*400000000000000^4483 ≤ 400051821164649^4483*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126772684330494707 3125000000000000000 400051821164649 400000000000000 1024 4483 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400051821164649/400000000000000 : ℝ)) (X := (3126772684330494707/3125000000000000000 : ℝ)) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1493629359734189/25000000000000000000 : ℝ) ≤ ((185320698398798519/185360000000000000 : ℝ)+2*(10226036711/9268000000000 : ℝ)*(2169/20000 : ℝ))^(4483/1024 : ℝ) := by
    rw [show (185320698398798519/185360000000000000 : ℝ)+2*(10226036711/9268000000000 : ℝ)*(2169/20000 : ℝ)=(80002183403561/80000000000000 : ℝ) by norm_num, show 1+2*(1493629359734189/25000000000000000000 : ℝ)=(12501493629359734189/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1772684330494707/6250000000000000000 : ℝ)+(1493629359734189/25000000000000000000 : ℝ) ≤ ((185320698398798519/185360000000000000 : ℝ)+(10226036711/9268000000000 : ℝ)*((15479/100000 : ℝ)+(2169/20000 : ℝ)))^(4483/1024 : ℝ) := by
    rw [show (185320698398798519/185360000000000000 : ℝ)+(10226036711/9268000000000 : ℝ)*((15479/100000 : ℝ)+(2169/20000 : ℝ))=(400031369091227/400000000000000 : ℝ) by norm_num, show 1+(1772684330494707/6250000000000000000 : ℝ)+(1493629359734189/25000000000000000000 : ℝ)=(25008584366681713017/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1772684330494707/6250000000000000000 : ℝ) ≤ ((185320698398798519/185360000000000000 : ℝ)+2*(10226036711/9268000000000 : ℝ)*(15479/100000 : ℝ))^(4483/1024 : ℝ) := by
    rw [show (185320698398798519/185360000000000000 : ℝ)+2*(10226036711/9268000000000 : ℝ)*(15479/100000 : ℝ)=(400051821164649/400000000000000 : ℝ) by norm_num, show 1+2*(1772684330494707/6250000000000000000 : ℝ)=(3126772684330494707/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (185320698398798519/185360000000000000 : ℝ)*(X 1 0+X 2 0)+(10226036711/9268000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4483/1024 : ℝ)) (lo := (2169/20000 : ℝ)) (hi := (15479/100000 : ℝ)) (c := (185320698398798519/185360000000000000 : ℝ)) (alpha := (10226036711/9268000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (185320698398798519/185360000000000000 : ℝ)*(X 0 1+X 2 1)+(10226036711/9268000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4483/1024 : ℝ)) (lo := (2169/20000 : ℝ)) (hi := (15479/100000 : ℝ)) (c := (185320698398798519/185360000000000000 : ℝ)) (alpha := (10226036711/9268000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (185320698398798519/185360000000000000 : ℝ)*(X 0 2+X 1 2)+(10226036711/9268000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4483/1024 : ℝ)) (lo := (2169/20000 : ℝ)) (hi := (15479/100000 : ℝ)) (c := (185320698398798519/185360000000000000 : ℝ)) (alpha := (10226036711/9268000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-104877277/625000000 : ℝ)*X 0 0+(5404781829/10000000000 : ℝ)*X 0 1+(1351195481/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1317626321/2500000000 : ℝ)*X 1 0+(-233019577/1250000000 : ℝ)*X 1 1+(2702390747/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2635252207/5000000000 : ℝ)*X 2 0+(5404782077/10000000000 : ℝ)*X 2 1+(-932078501/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4482135791/10000000000 : ℝ)*X 0 0+(4183377803/10000000000 : ℝ)*X 0 1+(4183376487/10000000000 : ℝ)*X 0 2+(4482135791/10000000000 : ℝ)*X 1 0+(4183377803/10000000000 : ℝ)*X 1 1+(4183376487/10000000000 : ℝ)*X 1 2+(4482135791/10000000000 : ℝ)*X 2 0+(4183377803/10000000000 : ℝ)*X 2 1+(4183376487/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-529324071/2500000000 : ℝ)*X 0 0+(2621497847/5000000000 : ℝ)*X 0 1+(2621498133/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1345825399/2500000000 : ℝ)*X 1 0+(-386121529/2000000000 : ℝ)*X 1 1+(2621497937/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((336456313/625000000 : ℝ)*X 2 0+(41943971/80000000 : ℝ)*X 2 1+(-1930607769/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((814398499/2000000000 : ℝ)*X 0 0+(4388312267/10000000000 : ℝ)*X 0 1+(438831193/1000000000 : ℝ)*X 0 2+(814398499/2000000000 : ℝ)*X 1 0+(4388312267/10000000000 : ℝ)*X 1 1+(438831193/1000000000 : ℝ)*X 1 2+(814398499/2000000000 : ℝ)*X 2 0+(4388312267/10000000000 : ℝ)*X 2 1+(438831193/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2024569891/10000000000 : ℝ)*X 0 0+(1282463587/2500000000 : ℝ)*X 0 1+(5425287627/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5256201521/10000000000 : ℝ)*X 1 0+(-231935471/1250000000 : ℝ)*X 1 1+(135632183/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1314050201/2500000000 : ℝ)*X 2 0+(5425288261/10000000000 : ℝ)*X 2 1+(-463870863/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((566620797/1250000000 : ℝ)*X 0 0+(2078685349/5000000000 : ℝ)*X 0 1+(259835639/625000000 : ℝ)*X 0 2+(566620797/1250000000 : ℝ)*X 1 0+(2078685349/5000000000 : ℝ)*X 1 1+(259835639/625000000 : ℝ)*X 1 2+(566620797/1250000000 : ℝ)*X 2 0+(2078685349/5000000000 : ℝ)*X 2 1+(259835639/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1770812403/10000000000 : ℝ)*X 0 0+(2757111387/5000000000 : ℝ)*X 0 1+(5227986597/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2696882741/5000000000 : ℝ)*X 1 0+(-968295737/5000000000 : ℝ)*X 1 1+(163374561/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5393765133/10000000000 : ℝ)*X 2 0+(1045597299/2000000000 : ℝ)*X 2 1+(-1936591219/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4033081887/10000000000 : ℝ)*X 0 0+(2203651519/5000000000 : ℝ)*X 0 1+(1101825437/2500000000 : ℝ)*X 0 2+(4033081887/10000000000 : ℝ)*X 1 0+(2203651519/5000000000 : ℝ)*X 1 1+(1101825437/2500000000 : ℝ)*X 1 2+(4033081887/10000000000 : ℝ)*X 2 0+(2203651519/5000000000 : ℝ)*X 2 1+(1101825437/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-63717/100000 : ℝ) ≤ (-147626894272609738965796227/231700000000000000000000000 : ℝ) := by norm_num
    linear_combination (12349853/10000000000000 : ℝ)*(upper1) + (135918237/100000000000000 : ℝ)*(lower4) + (14761327/100000000000000 : ℝ)*(upper5) + (1098347563832467/50000000000000 : ℝ)*(major0) + (1098347563832467/50000000000000 : ℝ)*(major1) + (1098347563832467/50000000000000 : ℝ)*(major2) + (193677679/12500000000000 : ℝ)*(sp3) + (152907973078731/5000000000000 : ℝ)*(sp4) + (3058157050907261/100000000000000 : ℝ)*(sp5) + (1529057548240093/50000000000000 : ℝ)*(sp6) + (1356463034550899/100000000000000 : ℝ)*(sp7) + (4433674809/100000000000000 : ℝ)*(sp12) + (6844342169/100000000000000 : ℝ)*(sp13) + (9759753849/20000000000000 : ℝ)*(sp14) + (135646458397233/10000000000000 : ℝ)*(f.failure) + (305816389524943/10000000000000 : ℝ)*(f.sum) + (9853141/289625000000000000000000 : ℝ)*base65 + (46015254864956373/9268000000000000000000000000000 : ℝ)*base67 + (19024429444460373/9268000000000000000000000000000 : ℝ)*base69 + (40192760317548373/9268000000000000000000000000000 : ℝ)*base71 + (1932115326289/579250000000000000000000000 : ℝ)*base74 + (50892872361751627/9268000000000000000000000000000 : ℝ)*base76 + (52497092113263627/9268000000000000000000000000000 : ℝ)*base78 + (51494166281215627/9268000000000000000000000000000 : ℝ)*base80 + (1867289677027/463400000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base87 + (3300547/500000000000000000000 : ℝ)*base90 + (3300547/500000000000000000000 : ℝ)*base92 + (3300547/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (58543/100000 : ℝ) ≤ (48446508720332583328529332293/82750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5851759/2500000000000 : ℝ)*(lower0) + (62393/50000000000000 : ℝ)*(upper1) + (213149871/100000000000000 : ℝ)*(upper2) + (89615791/100000000000000 : ℝ)*(upper3) + (8333761/50000000000000 : ℝ)*(lower5) + (283963617050157/12500000000000 : ℝ)*(major0) + (283963617050157/12500000000000 : ℝ)*(major1) + (283963617050157/12500000000000 : ℝ)*(major2) + (97534902172957/3125000000000 : ℝ)*(sp0) + (780251944764963/25000000000000 : ℝ)*(sp1) + (3121048597865659/100000000000000 : ℝ)*(sp2) + (35069644832751/2500000000000 : ℝ)*(sp3) + (109090474771/100000000000000 : ℝ)*(sp9) + (17067917241/25000000000000 : ℝ)*(sp10) + (35069644832751/2500000000000 : ℝ)*(f.failure) + (97534902172957/3125000000000 : ℝ)*(f.sum) + (45277539891/144812500000000000000000000 : ℝ)*base65 + (23703680955985483/2317000000000000000000000000000 : ℝ)*base67 + (32897331118894517/2317000000000000000000000000000 : ℝ)*base70 + (19602505498074483/2317000000000000000000000000000 : ℝ)*base71 + (123706895659/57925000000000000000000000 : ℝ)*base73 + (2768606624961483/2317000000000000000000000000000 : ℝ)*base75 + (12010666804383483/2317000000000000000000000000000 : ℝ)*base77 + (14429475911818483/2317000000000000000000000000000 : ℝ)*base79 + (734452113749/1158500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (810909/125000000000000000000 : ℝ)*base90 + (810909/125000000000000000000 : ℝ)*base92 + (810909/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (20031/25000 : ℝ) ≤ (928259890692598180130882461407/1158500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19803163/25000000000000 : ℝ)*(upper1) + (14876587/50000000000000 : ℝ)*(upper2) + (3036149/20000000000000 : ℝ)*(lower5) + (308460956657949/12500000000000 : ℝ)*(major0) + (308460956657949/12500000000000 : ℝ)*(major1) + (308460956657949/12500000000000 : ℝ)*(major2) + (188559711/50000000000000 : ℝ)*(sp0) + (148872584867/100000000000000 : ℝ)*(sp2) + (1704053379/10000000000000 : ℝ)*(sp3) + (3384861917090173/100000000000000 : ℝ)*(sp8) + (3384863507044019/100000000000000 : ℝ)*(sp9) + (211544664653697/6250000000000 : ℝ)*(sp10) + (1523786087083667/100000000000000 : ℝ)*(sp11) + (151604303/12500000000000 : ℝ)*(sp12) + (1523803127617457/100000000000000 : ℝ)*(f.failure) + (3384863507044019/100000000000000 : ℝ)*(f.sum) + (4090490510489/2317000000000000000000000000 : ℝ)*base65 + (2505832201260469/2317000000000000000000000000000 : ℝ)*base68 + (1475632221752531/2317000000000000000000000000000 : ℝ)*base69 + (5351389532380531/2317000000000000000000000000000 : ℝ)*base71 + (1026926155061/289625000000000000000000000 : ℝ)*base74 + (6113021361548469/2317000000000000000000000000000 : ℝ)*base76 + (7485559124081531/2317000000000000000000000000000 : ℝ)*base77 + (1016086083218531/2317000000000000000000000000000 : ℝ)*base79 + (310284066867/115850000000000000000000000 : ℝ)*base82 + (28299837/5000000000000000000000 : ℝ)*base89 + (28299837/5000000000000000000000 : ℝ)*base91 + (28299837/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-17177/20000 : ℝ) ≤ (-397981120832291965219615797/463400000000000000000000000 : ℝ) := by norm_num
    linear_combination (104397783/100000000000000 : ℝ)*(lower0) + (4074869/5000000000000 : ℝ)*(upper1) + (162523/781250000000 : ℝ)*(lower2) + (12096121/20000000000000 : ℝ)*(upper3) + (13548453/25000000000000 : ℝ)*(upper5) + (62658055082689/2500000000000 : ℝ)*(major0) + (62658055082689/2500000000000 : ℝ)*(major1) + (62658055082689/2500000000000 : ℝ)*(major2) + (13919837/5000000000000 : ℝ)*(sp4) + (8525155119/6250000000000 : ℝ)*(sp5) + (21835073051343/625000000000 : ℝ)*(sp12) + (873368891032429/25000000000000 : ℝ)*(sp13) + (174680598330581/5000000000000 : ℝ)*(sp14) + (1547660056233699/100000000000000 : ℝ)*(sp15) + (1547660056233699/100000000000000 : ℝ)*(f.failure) + (174680598330581/5000000000000 : ℝ)*(f.sum) + (97242680721/2317000000000000000000000000 : ℝ)*base66 + (2050931008374791/463400000000000000000000000000 : ℝ)*base67 + (1476678233579209/463400000000000000000000000000 : ℝ)*base70 + (1467742262686991/463400000000000000000000000000 : ℝ)*base71 + (20798075394367/1158500000000000000000000000 : ℝ)*base73 + (2682851680054409/463400000000000000000000000000 : ℝ)*base76 + (577271392870609/463400000000000000000000000000 : ℝ)*base78 + (880958512626791/463400000000000000000000000000 : ℝ)*base79 + (1707984926497/289625000000000000000000000 : ℝ)*base81 + (17420359/5000000000000000000000 : ℝ)*base89 + (17420359/5000000000000000000000 : ℝ)*base91 + (17420359/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1494_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80971341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2169/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63717/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58543/100000 : ℝ) else (20031/25000 : ℝ) ≤ X j i ∧ X j i ≤ (17177/20000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1494_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1494_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80971341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (387/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10843/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63717/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58543/100000 : ℝ) else (20031/25000 : ℝ) ≤ X j i ∧ X j i ≤ (17177/20000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1494_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1494_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1494_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80971341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (387/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10843/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63717/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58543/100000 : ℝ) else (20031/25000 : ℝ) ≤ X j i ∧ X j i ≤ (17177/20000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1494_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

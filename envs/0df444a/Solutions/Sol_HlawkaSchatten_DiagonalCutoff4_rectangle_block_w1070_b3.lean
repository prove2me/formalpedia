-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1070_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:10:05.585991+00:00
-- url     : https://prove2.me/submissions/b045a1fd-0afc-4467-b20d-3237730512c1

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
theorem support_rectangle_w1070_s9_0 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2201803699/10000000000 : ℝ)*x 0 + (5394257747/10000000000 : ℝ)*x 1 + (2632276583/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2201803699/10000000000 : ℝ)^8263 ≤ (13372342438399/100000000000000 : ℝ)^6215 := by
    have hnat : (2201803699 : ℕ)^8263*100000000000000^6215 ≤ 13372342438399^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201803699 10000000000 13372342438399 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394257747/10000000000 : ℝ)^8263 ≤ (8802912588743/20000000000000 : ℝ)^6215 := by
    have hnat : (5394257747 : ℕ)^8263*20000000000000^6215 ≤ 8802912588743^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394257747 10000000000 8802912588743 20000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632276583/5000000000 : ℝ)^8263 ≤ (42613094600077/100000000000000 : ℝ)^6215 := by
    have hnat : (2632276583 : ℕ)^8263*100000000000000^6215 ≤ 42613094600077^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632276583 5000000000 42613094600077 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2201803699/10000000000 : ℝ), (5394257747/10000000000 : ℝ), (2632276583/5000000000 : ℝ)] ![(13372342438399/100000000000000 : ℝ), (8802912588743/20000000000000 : ℝ), (42613094600077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2201803699/10000000000 : ℝ)|^8263 ≤ (13372342438399/100000000000000 : ℝ)^6215
        have hw : |(-2201803699/10000000000 : ℝ)|=(2201803699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394257747/10000000000 : ℝ)|^8263 ≤ (8802912588743/20000000000000 : ℝ)^6215
        have hw : |(5394257747/10000000000 : ℝ)|=(5394257747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632276583/5000000000 : ℝ)|^8263 ≤ (42613094600077/100000000000000 : ℝ)^6215
        have hw : |(2632276583/5000000000 : ℝ)|=(2632276583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s9_1 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344962241/10000000000 : ℝ)*x 0 + (-2267610397/10000000000 : ℝ)*x 1 + (1316138233/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344962241/10000000000 : ℝ)^8263 ≤ (43480597807663/100000000000000 : ℝ)^6215 := by
    have hnat : (5344962241 : ℕ)^8263*100000000000000^6215 ≤ 43480597807663^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344962241 10000000000 43480597807663 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2267610397/10000000000 : ℝ)^8263 ≤ (6953155044909/50000000000000 : ℝ)^6215 := by
    have hnat : (2267610397 : ℕ)^8263*50000000000000^6215 ≤ 6953155044909^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2267610397 10000000000 6953155044909 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316138233/2500000000 : ℝ)^8263 ≤ (8522618416371/20000000000000 : ℝ)^6215 := by
    have hnat : (1316138233 : ℕ)^8263*20000000000000^6215 ≤ 8522618416371^6215*2500000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316138233 2500000000 8522618416371 20000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344962241/10000000000 : ℝ), (-2267610397/10000000000 : ℝ), (1316138233/2500000000 : ℝ)] ![(43480597807663/100000000000000 : ℝ), (6953155044909/50000000000000 : ℝ), (8522618416371/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344962241/10000000000 : ℝ)|^8263 ≤ (43480597807663/100000000000000 : ℝ)^6215
        have hw : |(5344962241/10000000000 : ℝ)|=(5344962241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2267610397/10000000000 : ℝ)|^8263 ≤ (6953155044909/50000000000000 : ℝ)^6215
        have hw : |(-2267610397/10000000000 : ℝ)|=(2267610397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316138233/2500000000 : ℝ)|^8263 ≤ (8522618416371/20000000000000 : ℝ)^6215
        have hw : |(1316138233/2500000000 : ℝ)|=(1316138233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s9_2 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672481157/5000000000 : ℝ)*x 0 + (526455307/1000000000 : ℝ)*x 1 + (-1133805059/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672481157/5000000000 : ℝ)^8263 ≤ (10870149649299/25000000000000 : ℝ)^6215 := by
    have hnat : (2672481157 : ℕ)^8263*25000000000000^6215 ≤ 10870149649299^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672481157 5000000000 10870149649299 25000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526455307/1000000000 : ℝ)^8263 ≤ (42613093566961/100000000000000 : ℝ)^6215 := by
    have hnat : (526455307 : ℕ)^8263*100000000000000^6215 ≤ 42613093566961^6215*1000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526455307 1000000000 42613093566961 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1133805059/5000000000 : ℝ)^8263 ≤ (13906307815013/100000000000000 : ℝ)^6215 := by
    have hnat : (1133805059 : ℕ)^8263*100000000000000^6215 ≤ 13906307815013^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133805059 5000000000 13906307815013 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672481157/5000000000 : ℝ), (526455307/1000000000 : ℝ), (-1133805059/5000000000 : ℝ)] ![(10870149649299/25000000000000 : ℝ), (42613093566961/100000000000000 : ℝ), (13906307815013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672481157/5000000000 : ℝ)|^8263 ≤ (10870149649299/25000000000000 : ℝ)^6215
        have hw : |(2672481157/5000000000 : ℝ)|=(2672481157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526455307/1000000000 : ℝ)|^8263 ≤ (42613093566961/100000000000000 : ℝ)^6215
        have hw : |(526455307/1000000000 : ℝ)|=(526455307/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1133805059/5000000000 : ℝ)|^8263 ≤ (13906307815013/100000000000000 : ℝ)^6215
        have hw : |(-1133805059/5000000000 : ℝ)|=(1133805059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s9_3 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4374918761/10000000000 : ℝ)*x 0 + (4249587977/10000000000 : ℝ)*x 1 + (1125998181/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4374918761/10000000000 : ℝ)^8263 ≤ (33316587138939/100000000000000 : ℝ)^6215 := by
    have hnat : (4374918761 : ℕ)^8263*100000000000000^6215 ≤ 33316587138939^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374918761 10000000000 33316587138939 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4249587977/10000000000 : ℝ)^8263 ≤ (3205366435417/10000000000000 : ℝ)^6215 := by
    have hnat : (4249587977 : ℕ)^8263*10000000000000^6215 ≤ 3205366435417^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249587977 10000000000 3205366435417 10000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1125998181/2500000000 : ℝ)^8263 ≤ (2164359280897/6250000000000 : ℝ)^6215 := by
    have hnat : (1125998181 : ℕ)^8263*6250000000000^6215 ≤ 2164359280897^6215*2500000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125998181 2500000000 2164359280897 6250000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4374918761/10000000000 : ℝ), (4249587977/10000000000 : ℝ), (1125998181/2500000000 : ℝ)] ![(33316587138939/100000000000000 : ℝ), (3205366435417/10000000000000 : ℝ), (2164359280897/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4374918761/10000000000 : ℝ)|^8263 ≤ (33316587138939/100000000000000 : ℝ)^6215
        have hw : |(4374918761/10000000000 : ℝ)|=(4374918761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4249587977/10000000000 : ℝ)|^8263 ≤ (3205366435417/10000000000000 : ℝ)^6215
        have hw : |(4249587977/10000000000 : ℝ)|=(4249587977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1125998181/2500000000 : ℝ)|^8263 ≤ (2164359280897/6250000000000 : ℝ)^6215
        have hw : |(1125998181/2500000000 : ℝ)|=(1125998181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s9_4 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-550452173/2500000000 : ℝ)*x 0 + (5264878069/10000000000 : ℝ)*x 1 + (1348482929/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (550452173/2500000000 : ℝ)^8263 ≤ (13372382755309/100000000000000 : ℝ)^6215 := by
    have hnat : (550452173 : ℕ)^8263*100000000000000^6215 ≤ 13372382755309^6215*2500000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550452173 2500000000 13372382755309 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264878069/10000000000 : ℝ)^8263 ≤ (21308295561241/50000000000000 : ℝ)^6215 := by
    have hnat : (5264878069 : ℕ)^8263*50000000000000^6215 ≤ 21308295561241^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264878069 10000000000 21308295561241 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348482929/2500000000 : ℝ)^8263 ≤ (44011026099829/100000000000000 : ℝ)^6215 := by
    have hnat : (1348482929 : ℕ)^8263*100000000000000^6215 ≤ 44011026099829^6215*2500000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348482929 2500000000 44011026099829 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-550452173/2500000000 : ℝ), (5264878069/10000000000 : ℝ), (1348482929/2500000000 : ℝ)] ![(13372382755309/100000000000000 : ℝ), (21308295561241/50000000000000 : ℝ), (44011026099829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-550452173/2500000000 : ℝ)|^8263 ≤ (13372382755309/100000000000000 : ℝ)^6215
        have hw : |(-550452173/2500000000 : ℝ)|=(550452173/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264878069/10000000000 : ℝ)|^8263 ≤ (21308295561241/50000000000000 : ℝ)^6215
        have hw : |(5264878069/10000000000 : ℝ)|=(5264878069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348482929/2500000000 : ℝ)|^8263 ≤ (44011026099829/100000000000000 : ℝ)^6215
        have hw : |(1348482929/2500000000 : ℝ)|=(1348482929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s9_5 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312281701/10000000000 : ℝ)*x 0 + (-1069115809/5000000000 : ℝ)*x 1 + (269696589/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312281701/10000000000 : ℝ)^8263 ≤ (2156374863513/5000000000000 : ℝ)^6215 := by
    have hnat : (5312281701 : ℕ)^8263*5000000000000^6215 ≤ 2156374863513^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312281701 10000000000 2156374863513 5000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1069115809/5000000000 : ℝ)^8263 ≤ (1607684488901/12500000000000 : ℝ)^6215 := by
    have hnat : (1069115809 : ℕ)^8263*12500000000000^6215 ≤ 1607684488901^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069115809 5000000000 1607684488901 12500000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269696589/500000000 : ℝ)^8263 ≤ (22005513397053/50000000000000 : ℝ)^6215 := by
    have hnat : (269696589 : ℕ)^8263*50000000000000^6215 ≤ 22005513397053^6215*500000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269696589 500000000 22005513397053 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312281701/10000000000 : ℝ), (-1069115809/5000000000 : ℝ), (269696589/500000000 : ℝ)] ![(2156374863513/5000000000000 : ℝ), (1607684488901/12500000000000 : ℝ), (22005513397053/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312281701/10000000000 : ℝ)|^8263 ≤ (2156374863513/5000000000000 : ℝ)^6215
        have hw : |(5312281701/10000000000 : ℝ)|=(5312281701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1069115809/5000000000 : ℝ)|^8263 ≤ (1607684488901/12500000000000 : ℝ)^6215
        have hw : |(-1069115809/5000000000 : ℝ)|=(1069115809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269696589/500000000 : ℝ)|^8263 ≤ (22005513397053/50000000000000 : ℝ)^6215
        have hw : |(269696589/500000000 : ℝ)|=(269696589/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s9_6 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2187464293/5000000000 : ℝ)*x 0 + (2251677867/5000000000 : ℝ)*x 1 + (4250227339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187464293/5000000000 : ℝ)^8263 ≤ (8329171653823/25000000000000 : ℝ)^6215 := by
    have hnat : (2187464293 : ℕ)^8263*25000000000000^6215 ≤ 8329171653823^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187464293 5000000000 8329171653823 25000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2251677867/5000000000 : ℝ)^8263 ≤ (34623237148389/100000000000000 : ℝ)^6215 := by
    have hnat : (2251677867 : ℕ)^8263*100000000000000^6215 ≤ 34623237148389^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251677867 5000000000 34623237148389 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4250227339/10000000000 : ℝ)^8263 ≤ (32060076229449/100000000000000 : ℝ)^6215 := by
    have hnat : (4250227339 : ℕ)^8263*100000000000000^6215 ≤ 32060076229449^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4250227339 10000000000 32060076229449 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187464293/5000000000 : ℝ), (2251677867/5000000000 : ℝ), (4250227339/10000000000 : ℝ)] ![(8329171653823/25000000000000 : ℝ), (34623237148389/100000000000000 : ℝ), (32060076229449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187464293/5000000000 : ℝ)|^8263 ≤ (8329171653823/25000000000000 : ℝ)^6215
        have hw : |(2187464293/5000000000 : ℝ)|=(2187464293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2251677867/5000000000 : ℝ)|^8263 ≤ (34623237148389/100000000000000 : ℝ)^6215
        have hw : |(2251677867/5000000000 : ℝ)|=(2251677867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4250227339/10000000000 : ℝ)|^8263 ≤ (32060076229449/100000000000000 : ℝ)^6215
        have hw : |(4250227339/10000000000 : ℝ)|=(4250227339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1070_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74035429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2801/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11257/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5629/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2801/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2801/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11257/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2801/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11257/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2801/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11257/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2801/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11257/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2801/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11257/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2801/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11257/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11257/100000 : ℝ) ^ (4131/1024 : ℝ) ≤ (3725706128509059/25000000000000000000 : ℝ) := by
    have hpowers : (11257/100000 : ℝ)^4131 ≤ (3725706128509059/25000000000000000000 : ℝ)^1024 := by
      have hnat : (11257 : ℕ)^4131*25000000000000000000^1024 ≤ 3725706128509059^1024*100000^4131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11257 100000 3725706128509059 25000000000000000000 4131 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11257/100000 : ℝ)) (X := (3725706128509059/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2801/20000 : ℝ) ^ (4131/1024 : ℝ) ≤ (35971013648522673/100000000000000000000 : ℝ) := by
    have hpowers : (2801/20000 : ℝ)^4131 ≤ (35971013648522673/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2801 : ℕ)^4131*100000000000000000000^1024 ≤ 35971013648522673^1024*20000^4131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2801 20000 35971013648522673 100000000000000000000 4131 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2801/20000 : ℝ)) (X := (35971013648522673/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503725706128509059/12500000000000000000 : ℝ) ≤ (2500184686299923/2500000000000000 : ℝ) ^ (4131/1024 : ℝ) := by
    have hpowers : (12503725706128509059/12500000000000000000 : ℝ)^1024 ≤ (2500184686299923/2500000000000000 : ℝ)^4131 := by
      have hnat : (12503725706128509059 : ℕ)^1024*2500000000000000^4131 ≤ 2500184686299923^4131*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503725706128509059 12500000000000000000 2500184686299923 2500000000000000 1024 4131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500184686299923/2500000000000000 : ℝ)) (X := (12503725706128509059/12500000000000000000 : ℝ)) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050873838162558909/100000000000000000000 : ℝ) ≤ (625078801813551/625000000000000 : ℝ) ^ (4131/1024 : ℝ) := by
    have hpowers : (100050873838162558909/100000000000000000000 : ℝ)^1024 ≤ (625078801813551/625000000000000 : ℝ)^4131 := by
      have hnat : (100050873838162558909 : ℕ)^1024*625000000000000^4131 ≤ 625078801813551^4131*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050873838162558909 100000000000000000000 625078801813551 625000000000000 1024 4131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625078801813551/625000000000000 : ℝ)) (X := (100050873838162558909/100000000000000000000 : ℝ)) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035971013648522673/50000000000000000000 : ℝ) ≤ (500089145641697/500000000000000 : ℝ) ^ (4131/1024 : ℝ) := by
    have hpowers : (50035971013648522673/50000000000000000000 : ℝ)^1024 ≤ (500089145641697/500000000000000 : ℝ)^4131 := by
      have hnat : (50035971013648522673 : ℕ)^1024*500000000000000^4131 ≤ 500089145641697^4131*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035971013648522673 50000000000000000000 500089145641697 500000000000000 1024 4131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500089145641697/500000000000000 : ℝ)) (X := (50035971013648522673/50000000000000000000 : ℝ)) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3725706128509059/25000000000000000000 : ℝ) ≤ ((686756896918750597/687000000000000000 : ℝ)+2*(130520954281/68700000000000 : ℝ)*(11257/100000 : ℝ))^(4131/1024 : ℝ) := by
    rw [show (686756896918750597/687000000000000000 : ℝ)+2*(130520954281/68700000000000 : ℝ)*(11257/100000 : ℝ)=(2500184686299923/2500000000000000 : ℝ) by norm_num, show 1+2*(3725706128509059/25000000000000000000 : ℝ)=(12503725706128509059/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35971013648522673/100000000000000000000 : ℝ)+(3725706128509059/25000000000000000000 : ℝ) ≤ ((686756896918750597/687000000000000000 : ℝ)+(130520954281/68700000000000 : ℝ)*((2801/20000 : ℝ)+(11257/100000 : ℝ)))^(4131/1024 : ℝ) := by
    rw [show (686756896918750597/687000000000000000 : ℝ)+(130520954281/68700000000000 : ℝ)*((2801/20000 : ℝ)+(11257/100000 : ℝ))=(625078801813551/625000000000000 : ℝ) by norm_num, show 1+(35971013648522673/100000000000000000000 : ℝ)+(3725706128509059/25000000000000000000 : ℝ)=(100050873838162558909/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35971013648522673/100000000000000000000 : ℝ) ≤ ((686756896918750597/687000000000000000 : ℝ)+2*(130520954281/68700000000000 : ℝ)*(2801/20000 : ℝ))^(4131/1024 : ℝ) := by
    rw [show (686756896918750597/687000000000000000 : ℝ)+2*(130520954281/68700000000000 : ℝ)*(2801/20000 : ℝ)=(500089145641697/500000000000000 : ℝ) by norm_num, show 1+2*(35971013648522673/100000000000000000000 : ℝ)=(50035971013648522673/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (686756896918750597/687000000000000000 : ℝ)*(X 1 0+X 2 0)+(130520954281/68700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4131/1024 : ℝ)) (lo := (11257/100000 : ℝ)) (hi := (2801/20000 : ℝ)) (c := (686756896918750597/687000000000000000 : ℝ)) (alpha := (130520954281/68700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (686756896918750597/687000000000000000 : ℝ)*(X 0 1+X 2 1)+(130520954281/68700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4131/1024 : ℝ)) (lo := (11257/100000 : ℝ)) (hi := (2801/20000 : ℝ)) (c := (686756896918750597/687000000000000000 : ℝ)) (alpha := (130520954281/68700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (686756896918750597/687000000000000000 : ℝ)*(X 0 2+X 1 2)+(130520954281/68700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4131/1024 : ℝ)) (lo := (11257/100000 : ℝ)) (hi := (2801/20000 : ℝ)) (c := (686756896918750597/687000000000000000 : ℝ)) (alpha := (130520954281/68700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2201803699/10000000000 : ℝ)*X 0 0+(5394257747/10000000000 : ℝ)*X 0 1+(2632276583/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344962241/10000000000 : ℝ)*X 1 0+(-2267610397/10000000000 : ℝ)*X 1 1+(1316138233/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672481157/5000000000 : ℝ)*X 2 0+(526455307/1000000000 : ℝ)*X 2 1+(-1133805059/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4374918761/10000000000 : ℝ)*X 0 0+(4249587977/10000000000 : ℝ)*X 0 1+(1125998181/2500000000 : ℝ)*X 0 2+(4374918761/10000000000 : ℝ)*X 1 0+(4249587977/10000000000 : ℝ)*X 1 1+(1125998181/2500000000 : ℝ)*X 1 2+(4374918761/10000000000 : ℝ)*X 2 0+(4249587977/10000000000 : ℝ)*X 2 1+(1125998181/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-550452173/2500000000 : ℝ)*X 0 0+(5264878069/10000000000 : ℝ)*X 0 1+(1348482929/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312281701/10000000000 : ℝ)*X 1 0+(-1069115809/5000000000 : ℝ)*X 1 1+(269696589/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s9_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2187464293/5000000000 : ℝ)*X 0 0+(2251677867/5000000000 : ℝ)*X 0 1+(4250227339/10000000000 : ℝ)*X 0 2+(2187464293/5000000000 : ℝ)*X 1 0+(2251677867/5000000000 : ℝ)*X 1 1+(4250227339/10000000000 : ℝ)*X 1 2+(2187464293/5000000000 : ℝ)*X 2 0+(2251677867/5000000000 : ℝ)*X 2 1+(4250227339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s9_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10094488338002505399597181/11450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (647827623/100000000000000 : ℝ)*(base19) + (694583483/100000000000000 : ℝ)*(base23) + (37842027/50000000000000 : ℝ)*(lower2) + (13107229/100000000000000 : ℝ)*(upper5) + (727539679026109/12500000000000 : ℝ)*(major0) + (727539679026109/12500000000000 : ℝ)*(major1) + (5820317432208873/100000000000000 : ℝ)*(major2) + (7709846503853609/100000000000000 : ℝ)*(sp0) + (7709855623084849/100000000000000 : ℝ)*(sp1) + (3854934580102207/50000000000000 : ℝ)*(sp2) + (3930753869923583/100000000000000 : ℝ)*(sp3) + (1459433393/6250000000000 : ℝ)*(sp4) + (424496107/3125000000000 : ℝ)*(sp5) + (11110319101/100000000000000 : ℝ)*(sp6) + (982691245060671/25000000000000 : ℝ)*(f.failure) + (7709869854787897/100000000000000 : ℝ)*(f.sum) + (588241581119/1374000000000000000000000000 : ℝ)*base66 + (52704113461521677/8587500000000000000000000000000 : ℝ)*base68 + (955554084779332819/68700000000000000000000000000000 : ℝ)*base70 + (67713682265196677/8587500000000000000000000000000 : ℝ)*base72 + (2165971126091/1374000000000000000000000000 : ℝ)*base74 + (1026022950807532819/68700000000000000000000000000000 : ℝ)*base76 + (1308779679689573/8587500000000000000000000000000 : ℝ)*base77 + (30450702581939573/8587500000000000000000000000000 : ℝ)*base79 + (3107791249333/3435000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (8512859/1250000000000000000000 : ℝ)*base89 + (8512859/1250000000000000000000 : ℝ)*base91 + (3987141/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1070_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74035429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2801/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11257/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5629/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2801/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1070_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1070_box_0 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2072480829/10000000000 : ℝ)*x 0 + (33608203/62500000 : ℝ)*x 1 + (2688656027/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2072480829/10000000000 : ℝ)^8263 ≤ (12338342664059/100000000000000 : ℝ)^6215 := by
    have hnat : (2072480829 : ℕ)^8263*100000000000000^6215 ≤ 12338342664059^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072480829 10000000000 12338342664059 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33608203/62500000 : ℝ)^8263 ≤ (5478853871357/12500000000000 : ℝ)^6215 := by
    have hnat : (33608203 : ℕ)^8263*12500000000000^6215 ≤ 5478853871357^6215*62500000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33608203 62500000 5478853871357 12500000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688656027/5000000000 : ℝ)^8263 ≤ (43830826354273/100000000000000 : ℝ)^6215 := by
    have hnat : (2688656027 : ℕ)^8263*100000000000000^6215 ≤ 43830826354273^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688656027 5000000000 43830826354273 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2072480829/10000000000 : ℝ), (33608203/62500000 : ℝ), (2688656027/5000000000 : ℝ)] ![(12338342664059/100000000000000 : ℝ), (5478853871357/12500000000000 : ℝ), (43830826354273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2072480829/10000000000 : ℝ)|^8263 ≤ (12338342664059/100000000000000 : ℝ)^6215
        have hw : |(-2072480829/10000000000 : ℝ)|=(2072480829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33608203/62500000 : ℝ)|^8263 ≤ (5478853871357/12500000000000 : ℝ)^6215
        have hw : |(33608203/62500000 : ℝ)|=(33608203/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688656027/5000000000 : ℝ)|^8263 ≤ (43830826354273/100000000000000 : ℝ)^6215
        have hw : |(2688656027/5000000000 : ℝ)|=(2688656027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_box_1 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5295249769/10000000000 : ℝ)*x 0 + (-109179123/500000000 : ℝ)*x 1 + (5377312407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295249769/10000000000 : ℝ)^8263 ≤ (42943757126727/100000000000000 : ℝ)^6215 := by
    have hnat : (5295249769 : ℕ)^8263*100000000000000^6215 ≤ 42943757126727^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295249769 10000000000 42943757126727 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (109179123/500000000 : ℝ)^8263 ≤ (6612706342847/50000000000000 : ℝ)^6215 := by
    have hnat : (109179123 : ℕ)^8263*50000000000000^6215 ≤ 6612706342847^6215*500000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109179123 500000000 6612706342847 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5377312407/10000000000 : ℝ)^8263 ≤ (43830830179751/100000000000000 : ℝ)^6215 := by
    have hnat : (5377312407 : ℕ)^8263*100000000000000^6215 ≤ 43830830179751^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377312407 10000000000 43830830179751 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295249769/10000000000 : ℝ), (-109179123/500000000 : ℝ), (5377312407/10000000000 : ℝ)] ![(42943757126727/100000000000000 : ℝ), (6612706342847/50000000000000 : ℝ), (43830830179751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295249769/10000000000 : ℝ)|^8263 ≤ (42943757126727/100000000000000 : ℝ)^6215
        have hw : |(5295249769/10000000000 : ℝ)|=(5295249769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-109179123/500000000 : ℝ)|^8263 ≤ (6612706342847/50000000000000 : ℝ)^6215
        have hw : |(-109179123/500000000 : ℝ)|=(109179123/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5377312407/10000000000 : ℝ)|^8263 ≤ (43830830179751/100000000000000 : ℝ)^6215
        have hw : |(5377312407/10000000000 : ℝ)|=(5377312407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_box_2 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (529525007/1000000000 : ℝ)*x 0 + (5377312061/10000000000 : ℝ)*x 1 + (-2183582521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529525007/1000000000 : ℝ)^8263 ≤ (4294376037219/10000000000000 : ℝ)^6215 := by
    have hnat : (529525007 : ℕ)^8263*10000000000000^6215 ≤ 4294376037219^6215*1000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529525007 1000000000 4294376037219 10000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377312061/10000000000 : ℝ)^8263 ≤ (10957706607533/25000000000000 : ℝ)^6215 := by
    have hnat : (5377312061 : ℕ)^8263*25000000000000^6215 ≤ 10957706607533^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377312061 10000000000 10957706607533 25000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2183582521/10000000000 : ℝ)^8263 ≤ (13225413176903/100000000000000 : ℝ)^6215 := by
    have hnat : (2183582521 : ℕ)^8263*100000000000000^6215 ≤ 13225413176903^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183582521 10000000000 13225413176903 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529525007/1000000000 : ℝ), (5377312061/10000000000 : ℝ), (-2183582521/10000000000 : ℝ)] ![(4294376037219/10000000000000 : ℝ), (10957706607533/25000000000000 : ℝ), (13225413176903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529525007/1000000000 : ℝ)|^8263 ≤ (4294376037219/10000000000000 : ℝ)^6215
        have hw : |(529525007/1000000000 : ℝ)|=(529525007/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377312061/10000000000 : ℝ)|^8263 ≤ (10957706607533/25000000000000 : ℝ)^6215
        have hw : |(5377312061/10000000000 : ℝ)|=(5377312061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2183582521/10000000000 : ℝ)|^8263 ≤ (13225413176903/100000000000000 : ℝ)^6215
        have hw : |(-2183582521/10000000000 : ℝ)|=(2183582521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_box_3 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1120814113/2500000000 : ℝ)*x 0 + (2161454467/5000000000 : ℝ)*x 1 + (2161454463/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1120814113/2500000000 : ℝ)^8263 ≤ (34417937229779/100000000000000 : ℝ)^6215 := by
    have hnat : (1120814113 : ℕ)^8263*100000000000000^6215 ≤ 34417937229779^6215*2500000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120814113 2500000000 34417937229779 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2161454467/5000000000 : ℝ)^8263 ≤ (4098878927237/12500000000000 : ℝ)^6215 := by
    have hnat : (2161454467 : ℕ)^8263*12500000000000^6215 ≤ 4098878927237^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161454467 5000000000 4098878927237 12500000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2161454463/5000000000 : ℝ)^8263 ≤ (128089966161/390625000000 : ℝ)^6215 := by
    have hnat : (2161454463 : ℕ)^8263*390625000000^6215 ≤ 128089966161^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161454463 5000000000 128089966161 390625000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1120814113/2500000000 : ℝ), (2161454467/5000000000 : ℝ), (2161454463/5000000000 : ℝ)] ![(34417937229779/100000000000000 : ℝ), (4098878927237/12500000000000 : ℝ), (128089966161/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1120814113/2500000000 : ℝ)|^8263 ≤ (34417937229779/100000000000000 : ℝ)^6215
        have hw : |(1120814113/2500000000 : ℝ)|=(1120814113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2161454467/5000000000 : ℝ)|^8263 ≤ (4098878927237/12500000000000 : ℝ)^6215
        have hw : |(2161454467/5000000000 : ℝ)|=(2161454467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2161454463/5000000000 : ℝ)|^8263 ≤ (128089966161/390625000000 : ℝ)^6215
        have hw : |(2161454463/5000000000 : ℝ)|=(2161454463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_box_4 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-583126469/2500000000 : ℝ)*x 0 + (5280151403/10000000000 : ℝ)*x 1 + (2640076273/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (583126469/2500000000 : ℝ)^8263 ≤ (14437909687437/100000000000000 : ℝ)^6215 := by
    have hnat : (583126469 : ℕ)^8263*100000000000000^6215 ≤ 14437909687437^6215*2500000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      583126469 2500000000 14437909687437 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5280151403/10000000000 : ℝ)^8263 ≤ (8556207798789/20000000000000 : ℝ)^6215 := by
    have hnat : (5280151403 : ℕ)^8263*20000000000000^6215 ≤ 8556207798789^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280151403 10000000000 8556207798789 20000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2640076273/5000000000 : ℝ)^8263 ≤ (4278105130649/10000000000000 : ℝ)^6215 := by
    have hnat : (2640076273 : ℕ)^8263*10000000000000^6215 ≤ 4278105130649^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640076273 5000000000 4278105130649 10000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-583126469/2500000000 : ℝ), (5280151403/10000000000 : ℝ), (2640076273/5000000000 : ℝ)] ![(14437909687437/100000000000000 : ℝ), (8556207798789/20000000000000 : ℝ), (4278105130649/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-583126469/2500000000 : ℝ)|^8263 ≤ (14437909687437/100000000000000 : ℝ)^6215
        have hw : |(-583126469/2500000000 : ℝ)|=(583126469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5280151403/10000000000 : ℝ)|^8263 ≤ (8556207798789/20000000000000 : ℝ)^6215
        have hw : |(5280151403/10000000000 : ℝ)|=(5280151403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2640076273/5000000000 : ℝ)|^8263 ≤ (4278105130649/10000000000000 : ℝ)^6215
        have hw : |(2640076273/5000000000 : ℝ)|=(2640076273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_box_5 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (536400569/1000000000 : ℝ)*x 0 + (-2221580669/10000000000 : ℝ)*x 1 + (2640076001/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536400569/1000000000 : ℝ)^8263 ≤ (10921670865101/25000000000000 : ℝ)^6215 := by
    have hnat : (536400569 : ℕ)^8263*25000000000000^6215 ≤ 10921670865101^6215*1000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536400569 1000000000 10921670865101 25000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2221580669/10000000000 : ℝ)^8263 ≤ (13532271073947/100000000000000 : ℝ)^6215 := by
    have hnat : (2221580669 : ℕ)^8263*100000000000000^6215 ≤ 13532271073947^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2221580669 10000000000 13532271073947 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2640076001/5000000000 : ℝ)^8263 ≤ (42781045446451/100000000000000 : ℝ)^6215 := by
    have hnat : (2640076001 : ℕ)^8263*100000000000000^6215 ≤ 42781045446451^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640076001 5000000000 42781045446451 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536400569/1000000000 : ℝ), (-2221580669/10000000000 : ℝ), (2640076001/5000000000 : ℝ)] ![(10921670865101/25000000000000 : ℝ), (13532271073947/100000000000000 : ℝ), (42781045446451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536400569/1000000000 : ℝ)|^8263 ≤ (10921670865101/25000000000000 : ℝ)^6215
        have hw : |(536400569/1000000000 : ℝ)|=(536400569/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2221580669/10000000000 : ℝ)|^8263 ≤ (13532271073947/100000000000000 : ℝ)^6215
        have hw : |(-2221580669/10000000000 : ℝ)|=(2221580669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2640076001/5000000000 : ℝ)|^8263 ≤ (42781045446451/100000000000000 : ℝ)^6215
        have hw : |(2640076001/5000000000 : ℝ)|=(2640076001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_box_6 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (536400623/1000000000 : ℝ)*x 0 + (5280151271/10000000000 : ℝ)*x 1 + (-2221580921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536400623/1000000000 : ℝ)^8263 ≤ (8737337861527/20000000000000 : ℝ)^6215 := by
    have hnat : (536400623 : ℕ)^8263*20000000000000^6215 ≤ 8737337861527^6215*1000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536400623 1000000000 8737337861527 20000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5280151271/10000000000 : ℝ)^8263 ≤ (5347629696503/12500000000000 : ℝ)^6215 := by
    have hnat : (5280151271 : ℕ)^8263*12500000000000^6215 ≤ 5347629696503^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280151271 10000000000 5347629696503 12500000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2221580921/10000000000 : ℝ)^8263 ≤ (3383068278693/25000000000000 : ℝ)^6215 := by
    have hnat : (2221580921 : ℕ)^8263*25000000000000^6215 ≤ 3383068278693^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2221580921 10000000000 3383068278693 25000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536400623/1000000000 : ℝ), (5280151271/10000000000 : ℝ), (-2221580921/10000000000 : ℝ)] ![(8737337861527/20000000000000 : ℝ), (5347629696503/12500000000000 : ℝ), (3383068278693/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536400623/1000000000 : ℝ)|^8263 ≤ (8737337861527/20000000000000 : ℝ)^6215
        have hw : |(536400623/1000000000 : ℝ)|=(536400623/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5280151271/10000000000 : ℝ)|^8263 ≤ (5347629696503/12500000000000 : ℝ)^6215
        have hw : |(5280151271/10000000000 : ℝ)|=(5280151271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2221580921/10000000000 : ℝ)|^8263 ≤ (3383068278693/25000000000000 : ℝ)^6215
        have hw : |(-2221580921/10000000000 : ℝ)|=(2221580921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_box_7 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4266250583/10000000000 : ℝ)*x 0 + (110784763/250000000 : ℝ)*x 1 + (138480949/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4266250583/10000000000 : ℝ)^8263 ≤ (6444173976937/20000000000000 : ℝ)^6215 := by
    have hnat : (4266250583 : ℕ)^8263*20000000000000^6215 ≤ 6444173976937^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4266250583 10000000000 6444173976937 20000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (110784763/250000000 : ℝ)^8263 ≤ (16944782912787/50000000000000 : ℝ)^6215 := by
    have hnat : (110784763 : ℕ)^8263*50000000000000^6215 ≤ 16944782912787^6215*250000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110784763 250000000 16944782912787 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (138480949/312500000 : ℝ)^8263 ≤ (8472391070021/25000000000000 : ℝ)^6215 := by
    have hnat : (138480949 : ℕ)^8263*25000000000000^6215 ≤ 8472391070021^6215*312500000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138480949 312500000 8472391070021 25000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4266250583/10000000000 : ℝ), (110784763/250000000 : ℝ), (138480949/312500000 : ℝ)] ![(6444173976937/20000000000000 : ℝ), (16944782912787/50000000000000 : ℝ), (8472391070021/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4266250583/10000000000 : ℝ)|^8263 ≤ (6444173976937/20000000000000 : ℝ)^6215
        have hw : |(4266250583/10000000000 : ℝ)|=(4266250583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(110784763/250000000 : ℝ)|^8263 ≤ (16944782912787/50000000000000 : ℝ)^6215
        have hw : |(110784763/250000000 : ℝ)|=(110784763/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(138480949/312500000 : ℝ)|^8263 ≤ (8472391070021/25000000000000 : ℝ)^6215
        have hw : |(138480949/312500000 : ℝ)|=(138480949/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_box_8 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2278218437/10000000000 : ℝ)*x 0 + (1303553713/2500000000 : ℝ)*x 1 + (5386913107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2278218437/10000000000 : ℝ)^8263 ≤ (13992868545993/100000000000000 : ℝ)^6215 := by
    have hnat : (2278218437 : ℕ)^8263*100000000000000^6215 ≤ 13992868545993^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2278218437 10000000000 13992868545993 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1303553713/2500000000 : ℝ)^8263 ≤ (42072227408887/100000000000000 : ℝ)^6215 := by
    have hnat : (1303553713 : ℕ)^8263*100000000000000^6215 ≤ 42072227408887^6215*2500000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303553713 2500000000 42072227408887 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386913107/10000000000 : ℝ)^8263 ≤ (43934904032719/100000000000000 : ℝ)^6215 := by
    have hnat : (5386913107 : ℕ)^8263*100000000000000^6215 ≤ 43934904032719^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386913107 10000000000 43934904032719 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2278218437/10000000000 : ℝ), (1303553713/2500000000 : ℝ), (5386913107/10000000000 : ℝ)] ![(13992868545993/100000000000000 : ℝ), (42072227408887/100000000000000 : ℝ), (43934904032719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2278218437/10000000000 : ℝ)|^8263 ≤ (13992868545993/100000000000000 : ℝ)^6215
        have hw : |(-2278218437/10000000000 : ℝ)|=(2278218437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1303553713/2500000000 : ℝ)|^8263 ≤ (42072227408887/100000000000000 : ℝ)^6215
        have hw : |(1303553713/2500000000 : ℝ)|=(1303553713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386913107/10000000000 : ℝ)|^8263 ≤ (43934904032719/100000000000000 : ℝ)^6215
        have hw : |(5386913107/10000000000 : ℝ)|=(5386913107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_box_9 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1057690501/2000000000 : ℝ)*x 0 + (-2179756171/10000000000 : ℝ)*x 1 + (5386913407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057690501/2000000000 : ℝ)^8263 ≤ (10717620673829/25000000000000 : ℝ)^6215 := by
    have hnat : (1057690501 : ℕ)^8263*25000000000000^6215 ≤ 10717620673829^6215*2000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057690501 2000000000 10717620673829 25000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2179756171/10000000000 : ℝ)^8263 ≤ (824663125061/6250000000000 : ℝ)^6215 := by
    have hnat : (2179756171 : ℕ)^8263*6250000000000^6215 ≤ 824663125061^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179756171 10000000000 824663125061 6250000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386913407/10000000000 : ℝ)^8263 ≤ (21967453642873/50000000000000 : ℝ)^6215 := by
    have hnat : (5386913407 : ℕ)^8263*50000000000000^6215 ≤ 21967453642873^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386913407 10000000000 21967453642873 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057690501/2000000000 : ℝ), (-2179756171/10000000000 : ℝ), (5386913407/10000000000 : ℝ)] ![(10717620673829/25000000000000 : ℝ), (824663125061/6250000000000 : ℝ), (21967453642873/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057690501/2000000000 : ℝ)|^8263 ≤ (10717620673829/25000000000000 : ℝ)^6215
        have hw : |(1057690501/2000000000 : ℝ)|=(1057690501/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2179756171/10000000000 : ℝ)|^8263 ≤ (824663125061/6250000000000 : ℝ)^6215
        have hw : |(-2179756171/10000000000 : ℝ)|=(2179756171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386913407/10000000000 : ℝ)|^8263 ≤ (21967453642873/50000000000000 : ℝ)^6215
        have hw : |(5386913407/10000000000 : ℝ)|=(5386913407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_box_10 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2644226237/5000000000 : ℝ)*x 0 + (1077382491/2000000000 : ℝ)*x 1 + (-272469687/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644226237/5000000000 : ℝ)^8263 ≤ (42870482361207/100000000000000 : ℝ)^6215 := by
    have hnat : (2644226237 : ℕ)^8263*100000000000000^6215 ≤ 42870482361207^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644226237 5000000000 42870482361207 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1077382491/2000000000 : ℝ)^8263 ≤ (43934896962809/100000000000000 : ℝ)^6215 := by
    have hnat : (1077382491 : ℕ)^8263*100000000000000^6215 ≤ 43934896962809^6215*2000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077382491 2000000000 43934896962809 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272469687/1250000000 : ℝ)^8263 ≤ (1319462066451/10000000000000 : ℝ)^6215 := by
    have hnat : (272469687 : ℕ)^8263*10000000000000^6215 ≤ 1319462066451^6215*1250000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272469687 1250000000 1319462066451 10000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644226237/5000000000 : ℝ), (1077382491/2000000000 : ℝ), (-272469687/1250000000 : ℝ)] ![(42870482361207/100000000000000 : ℝ), (43934896962809/100000000000000 : ℝ), (1319462066451/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644226237/5000000000 : ℝ)|^8263 ≤ (42870482361207/100000000000000 : ℝ)^6215
        have hw : |(2644226237/5000000000 : ℝ)|=(2644226237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1077382491/2000000000 : ℝ)|^8263 ≤ (43934896962809/100000000000000 : ℝ)^6215
        have hw : |(1077382491/2000000000 : ℝ)|=(1077382491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-272469687/1250000000 : ℝ)|^8263 ≤ (1319462066451/10000000000000 : ℝ)^6215
        have hw : |(-272469687/1250000000 : ℝ)|=(272469687/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_box_11 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2252213297/5000000000 : ℝ)*x 0 + (539022831/1250000000 : ℝ)*x 1 + (1078046009/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2252213297/5000000000 : ℝ)^8263 ≤ (34634183710517/100000000000000 : ℝ)^6215 := by
    have hnat : (2252213297 : ℕ)^8263*100000000000000^6215 ≤ 34634183710517^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252213297 5000000000 34634183710517 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539022831/1250000000 : ℝ)^8263 ≤ (16341450572423/50000000000000 : ℝ)^6215 := by
    have hnat : (539022831 : ℕ)^8263*50000000000000^6215 ≤ 16341450572423^6215*1250000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539022831 1250000000 16341450572423 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078046009/2500000000 : ℝ)^8263 ≤ (16341457565681/50000000000000 : ℝ)^6215 := by
    have hnat : (1078046009 : ℕ)^8263*50000000000000^6215 ≤ 16341457565681^6215*2500000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078046009 2500000000 16341457565681 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2252213297/5000000000 : ℝ), (539022831/1250000000 : ℝ), (1078046009/2500000000 : ℝ)] ![(34634183710517/100000000000000 : ℝ), (16341450572423/50000000000000 : ℝ), (16341457565681/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2252213297/5000000000 : ℝ)|^8263 ≤ (34634183710517/100000000000000 : ℝ)^6215
        have hw : |(2252213297/5000000000 : ℝ)|=(2252213297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539022831/1250000000 : ℝ)|^8263 ≤ (16341450572423/50000000000000 : ℝ)^6215
        have hw : |(539022831/1250000000 : ℝ)|=(539022831/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078046009/2500000000 : ℝ)|^8263 ≤ (16341457565681/50000000000000 : ℝ)^6215
        have hw : |(1078046009/2500000000 : ℝ)|=(1078046009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_box_12 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-425426837/2000000000 : ℝ)*x 0 + (5441917367/10000000000 : ℝ)*x 1 + (131803721/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (425426837/2000000000 : ℝ)^8263 ≤ (12772804575917/100000000000000 : ℝ)^6215 := by
    have hnat : (425426837 : ℕ)^8263*100000000000000^6215 ≤ 12772804575917^6215*2000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425426837 2000000000 12772804575917 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5441917367/10000000000 : ℝ)^8263 ≤ (1113308488139/2500000000000 : ℝ)^6215 := by
    have hnat : (5441917367 : ℕ)^8263*2500000000000^6215 ≤ 1113308488139^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441917367 10000000000 1113308488139 2500000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131803721/250000000 : ℝ)^8263 ≤ (5336856985187/12500000000000 : ℝ)^6215 := by
    have hnat : (131803721 : ℕ)^8263*12500000000000^6215 ≤ 5336856985187^6215*250000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131803721 250000000 5336856985187 12500000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-425426837/2000000000 : ℝ), (5441917367/10000000000 : ℝ), (131803721/250000000 : ℝ)] ![(12772804575917/100000000000000 : ℝ), (1113308488139/2500000000000 : ℝ), (5336856985187/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-425426837/2000000000 : ℝ)|^8263 ≤ (12772804575917/100000000000000 : ℝ)^6215
        have hw : |(-425426837/2000000000 : ℝ)|=(425426837/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5441917367/10000000000 : ℝ)|^8263 ≤ (1113308488139/2500000000000 : ℝ)^6215
        have hw : |(5441917367/10000000000 : ℝ)|=(5441917367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131803721/250000000 : ℝ)|^8263 ≤ (5336856985187/12500000000000 : ℝ)^6215
        have hw : |(131803721/250000000 : ℝ)|=(131803721/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_box_13 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1073933399/2000000000 : ℝ)*x 0 + (-2224651709/10000000000 : ℝ)*x 1 + (2636074449/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073933399/2000000000 : ℝ)^8263 ≤ (43747995888553/100000000000000 : ℝ)^6215 := by
    have hnat : (1073933399 : ℕ)^8263*100000000000000^6215 ≤ 43747995888553^6215*2000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073933399 2000000000 43747995888553 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2224651709/10000000000 : ℝ)^8263 ≤ (3389286897653/25000000000000 : ℝ)^6215 := by
    have hnat : (2224651709 : ℕ)^8263*25000000000000^6215 ≤ 3389286897653^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2224651709 10000000000 3389286897653 25000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636074449/5000000000 : ℝ)^8263 ≤ (2668428531623/6250000000000 : ℝ)^6215 := by
    have hnat : (2636074449 : ℕ)^8263*6250000000000^6215 ≤ 2668428531623^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636074449 5000000000 2668428531623 6250000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073933399/2000000000 : ℝ), (-2224651709/10000000000 : ℝ), (2636074449/5000000000 : ℝ)] ![(43747995888553/100000000000000 : ℝ), (3389286897653/25000000000000 : ℝ), (2668428531623/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073933399/2000000000 : ℝ)|^8263 ≤ (43747995888553/100000000000000 : ℝ)^6215
        have hw : |(1073933399/2000000000 : ℝ)|=(1073933399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2224651709/10000000000 : ℝ)|^8263 ≤ (3389286897653/25000000000000 : ℝ)^6215
        have hw : |(-2224651709/10000000000 : ℝ)|=(2224651709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636074449/5000000000 : ℝ)|^8263 ≤ (2668428531623/6250000000000 : ℝ)^6215
        have hw : |(2636074449/5000000000 : ℝ)|=(2636074449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_box_14 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2684833547/5000000000 : ℝ)*x 0 + (2636074359/5000000000 : ℝ)*x 1 + (-278081477/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684833547/5000000000 : ℝ)^8263 ≤ (21873998480459/50000000000000 : ℝ)^6215 := by
    have hnat : (2684833547 : ℕ)^8263*50000000000000^6215 ≤ 21873998480459^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684833547 5000000000 21873998480459 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2636074359/5000000000 : ℝ)^8263 ≤ (42694854567953/100000000000000 : ℝ)^6215 := by
    have hnat : (2636074359 : ℕ)^8263*100000000000000^6215 ≤ 42694854567953^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636074359 5000000000 42694854567953 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (278081477/1250000000 : ℝ)^8263 ≤ (3389287114387/25000000000000 : ℝ)^6215 := by
    have hnat : (278081477 : ℕ)^8263*25000000000000^6215 ≤ 3389287114387^6215*1250000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278081477 1250000000 3389287114387 25000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684833547/5000000000 : ℝ), (2636074359/5000000000 : ℝ), (-278081477/1250000000 : ℝ)] ![(21873998480459/50000000000000 : ℝ), (42694854567953/100000000000000 : ℝ), (3389287114387/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684833547/5000000000 : ℝ)|^8263 ≤ (21873998480459/50000000000000 : ℝ)^6215
        have hw : |(2684833547/5000000000 : ℝ)|=(2684833547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2636074359/5000000000 : ℝ)|^8263 ≤ (42694854567953/100000000000000 : ℝ)^6215
        have hw : |(2636074359/5000000000 : ℝ)|=(2636074359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-278081477/1250000000 : ℝ)|^8263 ≤ (3389287114387/25000000000000 : ℝ)^6215
        have hw : |(-278081477/1250000000 : ℝ)|=(278081477/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_box_15 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062036607/2500000000 : ℝ)*x 0 + (4440320409/10000000000 : ℝ)*x 1 + (1110080259/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062036607/2500000000 : ℝ)^8263 ≤ (400490110887/1250000000000 : ℝ)^6215 := by
    have hnat : (1062036607 : ℕ)^8263*1250000000000^6215 ≤ 400490110887^6215*2500000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062036607 2500000000 400490110887 1250000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4440320409/10000000000 : ℝ)^8263 ≤ (8495098091217/25000000000000 : ℝ)^6215 := by
    have hnat : (4440320409 : ℕ)^8263*25000000000000^6215 ≤ 8495098091217^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4440320409 10000000000 8495098091217 25000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1110080259/2500000000 : ℝ)^8263 ≤ (6796079748849/20000000000000 : ℝ)^6215 := by
    have hnat : (1110080259 : ℕ)^8263*20000000000000^6215 ≤ 6796079748849^6215*2500000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1110080259 2500000000 6796079748849 20000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062036607/2500000000 : ℝ), (4440320409/10000000000 : ℝ), (1110080259/2500000000 : ℝ)] ![(400490110887/1250000000000 : ℝ), (8495098091217/25000000000000 : ℝ), (6796079748849/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062036607/2500000000 : ℝ)|^8263 ≤ (400490110887/1250000000000 : ℝ)^6215
        have hw : |(1062036607/2500000000 : ℝ)|=(1062036607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4440320409/10000000000 : ℝ)|^8263 ≤ (8495098091217/25000000000000 : ℝ)^6215
        have hw : |(4440320409/10000000000 : ℝ)|=(4440320409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1110080259/2500000000 : ℝ)|^8263 ≤ (6796079748849/20000000000000 : ℝ)^6215
        have hw : |(1110080259/2500000000 : ℝ)|=(1110080259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1070_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74035429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2801/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5629/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(2489/4000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14811/25000 : ℝ) ∧ (15917/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41481/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2801/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5629/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2801/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5629/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2801/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5629/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2801/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5629/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2801/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5629/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2801/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5629/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5629/50000 : ℝ) ^ (4131/1024 : ℝ) ≤ (7454082985223067/50000000000000000000 : ℝ) := by
    have hpowers : (5629/50000 : ℝ)^4131 ≤ (7454082985223067/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5629 : ℕ)^4131*50000000000000000000^1024 ≤ 7454082985223067^1024*50000^4131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5629 50000 7454082985223067 50000000000000000000 4131 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5629/50000 : ℝ)) (X := (7454082985223067/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2801/20000 : ℝ) ^ (4131/1024 : ℝ) ≤ (35971013648522673/100000000000000000000 : ℝ) := by
    have hpowers : (2801/20000 : ℝ)^4131 ≤ (35971013648522673/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2801 : ℕ)^4131*100000000000000000000^1024 ≤ 35971013648522673^1024*20000^4131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2801 20000 35971013648522673 100000000000000000000 4131 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2801/20000 : ℝ)) (X := (35971013648522673/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007454082985223067/25000000000000000000 : ℝ) ≤ (10000739009950373/10000000000000000 : ℝ) ^ (4131/1024 : ℝ) := by
    have hpowers : (25007454082985223067/25000000000000000000 : ℝ)^1024 ≤ (10000739009950373/10000000000000000 : ℝ)^4131 := by
      have hnat : (25007454082985223067 : ℕ)^1024*10000000000000000^4131 ≤ 10000739009950373^4131*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007454082985223067 25000000000000000000 10000739009950373 10000000000000000 1024 4131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000739009950373/10000000000000000 : ℝ)) (X := (25007454082985223067/25000000000000000000 : ℝ)) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050879179618968807/100000000000000000000 : ℝ) ≤ (10001260961371193/10000000000000000 : ℝ) ^ (4131/1024 : ℝ) := by
    have hpowers : (100050879179618968807/100000000000000000000 : ℝ)^1024 ≤ (10001260961371193/10000000000000000 : ℝ)^4131 := by
      have hnat : (100050879179618968807 : ℕ)^1024*10000000000000000^4131 ≤ 10001260961371193^4131*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050879179618968807 100000000000000000000 10001260961371193 10000000000000000 1024 4131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001260961371193/10000000000000000 : ℝ)) (X := (100050879179618968807/100000000000000000000 : ℝ)) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035971013648522673/50000000000000000000 : ℝ) ≤ (10001782912792013/10000000000000000 : ℝ) ^ (4131/1024 : ℝ) := by
    have hpowers : (50035971013648522673/50000000000000000000 : ℝ)^1024 ≤ (10001782912792013/10000000000000000 : ℝ)^4131 := by
      have hnat : (50035971013648522673 : ℕ)^1024*10000000000000000^4131 ≤ 10001782912792013^4131*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035971013648522673 50000000000000000000 10001782912792013 10000000000000000 1024 4131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001782912792013/10000000000000000 : ℝ)) (X := (50035971013648522673/50000000000000000000 : ℝ)) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7454082985223067/50000000000000000000 : ℝ) ≤ ((27460277802142491511/27470000000000000000 : ℝ)+2*(26097571041/13735000000000 : ℝ)*(5629/50000 : ℝ))^(4131/1024 : ℝ) := by
    rw [show (27460277802142491511/27470000000000000000 : ℝ)+2*(26097571041/13735000000000 : ℝ)*(5629/50000 : ℝ)=(10000739009950373/10000000000000000 : ℝ) by norm_num, show 1+2*(7454082985223067/50000000000000000000 : ℝ)=(25007454082985223067/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35971013648522673/100000000000000000000 : ℝ)+(7454082985223067/50000000000000000000 : ℝ) ≤ ((27460277802142491511/27470000000000000000 : ℝ)+(26097571041/13735000000000 : ℝ)*((2801/20000 : ℝ)+(5629/50000 : ℝ)))^(4131/1024 : ℝ) := by
    rw [show (27460277802142491511/27470000000000000000 : ℝ)+(26097571041/13735000000000 : ℝ)*((2801/20000 : ℝ)+(5629/50000 : ℝ))=(10001260961371193/10000000000000000 : ℝ) by norm_num, show 1+(35971013648522673/100000000000000000000 : ℝ)+(7454082985223067/50000000000000000000 : ℝ)=(100050879179618968807/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35971013648522673/100000000000000000000 : ℝ) ≤ ((27460277802142491511/27470000000000000000 : ℝ)+2*(26097571041/13735000000000 : ℝ)*(2801/20000 : ℝ))^(4131/1024 : ℝ) := by
    rw [show (27460277802142491511/27470000000000000000 : ℝ)+2*(26097571041/13735000000000 : ℝ)*(2801/20000 : ℝ)=(10001782912792013/10000000000000000 : ℝ) by norm_num, show 1+2*(35971013648522673/100000000000000000000 : ℝ)=(50035971013648522673/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27460277802142491511/27470000000000000000 : ℝ)*(X 1 0+X 2 0)+(26097571041/13735000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4131/1024 : ℝ)) (lo := (5629/50000 : ℝ)) (hi := (2801/20000 : ℝ)) (c := (27460277802142491511/27470000000000000000 : ℝ)) (alpha := (26097571041/13735000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27460277802142491511/27470000000000000000 : ℝ)*(X 0 1+X 2 1)+(26097571041/13735000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4131/1024 : ℝ)) (lo := (5629/50000 : ℝ)) (hi := (2801/20000 : ℝ)) (c := (27460277802142491511/27470000000000000000 : ℝ)) (alpha := (26097571041/13735000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27460277802142491511/27470000000000000000 : ℝ)*(X 0 2+X 1 2)+(26097571041/13735000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4131/1024 : ℝ)) (lo := (5629/50000 : ℝ)) (hi := (2801/20000 : ℝ)) (c := (27460277802142491511/27470000000000000000 : ℝ)) (alpha := (26097571041/13735000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2072480829/10000000000 : ℝ)*X 0 0+(33608203/62500000 : ℝ)*X 0 1+(2688656027/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5295249769/10000000000 : ℝ)*X 1 0+(-109179123/500000000 : ℝ)*X 1 1+(5377312407/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((529525007/1000000000 : ℝ)*X 2 0+(5377312061/10000000000 : ℝ)*X 2 1+(-2183582521/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1120814113/2500000000 : ℝ)*X 0 0+(2161454467/5000000000 : ℝ)*X 0 1+(2161454463/5000000000 : ℝ)*X 0 2+(1120814113/2500000000 : ℝ)*X 1 0+(2161454467/5000000000 : ℝ)*X 1 1+(2161454463/5000000000 : ℝ)*X 1 2+(1120814113/2500000000 : ℝ)*X 2 0+(2161454467/5000000000 : ℝ)*X 2 1+(2161454463/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-583126469/2500000000 : ℝ)*X 0 0+(5280151403/10000000000 : ℝ)*X 0 1+(2640076273/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((536400569/1000000000 : ℝ)*X 1 0+(-2221580669/10000000000 : ℝ)*X 1 1+(2640076001/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((536400623/1000000000 : ℝ)*X 2 0+(5280151271/10000000000 : ℝ)*X 2 1+(-2221580921/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4266250583/10000000000 : ℝ)*X 0 0+(110784763/250000000 : ℝ)*X 0 1+(138480949/312500000 : ℝ)*X 0 2+(4266250583/10000000000 : ℝ)*X 1 0+(110784763/250000000 : ℝ)*X 1 1+(138480949/312500000 : ℝ)*X 1 2+(4266250583/10000000000 : ℝ)*X 2 0+(110784763/250000000 : ℝ)*X 2 1+(138480949/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2278218437/10000000000 : ℝ)*X 0 0+(1303553713/2500000000 : ℝ)*X 0 1+(5386913107/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1057690501/2000000000 : ℝ)*X 1 0+(-2179756171/10000000000 : ℝ)*X 1 1+(5386913407/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2644226237/5000000000 : ℝ)*X 2 0+(1077382491/2000000000 : ℝ)*X 2 1+(-272469687/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2252213297/5000000000 : ℝ)*X 0 0+(539022831/1250000000 : ℝ)*X 0 1+(1078046009/2500000000 : ℝ)*X 0 2+(2252213297/5000000000 : ℝ)*X 1 0+(539022831/1250000000 : ℝ)*X 1 1+(1078046009/2500000000 : ℝ)*X 1 2+(2252213297/5000000000 : ℝ)*X 2 0+(539022831/1250000000 : ℝ)*X 2 1+(1078046009/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-425426837/2000000000 : ℝ)*X 0 0+(5441917367/10000000000 : ℝ)*X 0 1+(131803721/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1073933399/2000000000 : ℝ)*X 1 0+(-2224651709/10000000000 : ℝ)*X 1 1+(2636074449/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2684833547/5000000000 : ℝ)*X 2 0+(2636074359/5000000000 : ℝ)*X 2 1+(-278081477/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1062036607/2500000000 : ℝ)*X 0 0+(4440320409/10000000000 : ℝ)*X 0 1+(1110080259/2500000000 : ℝ)*X 0 2+(1062036607/2500000000 : ℝ)*X 1 0+(4440320409/10000000000 : ℝ)*X 1 1+(1110080259/2500000000 : ℝ)*X 1 2+(1062036607/2500000000 : ℝ)*X 2 0+(4440320409/10000000000 : ℝ)*X 2 1+(1110080259/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-2489/4000 : ℝ) ≤ (-2670694098007637399979589204071/4292187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (99658797/100000000000000 : ℝ)*(upper1) + (2886013/12500000000000 : ℝ)*(lower4) + (96632407/100000000000000 : ℝ)*(upper5) + (6031464750847/156250000000 : ℝ)*(major0) + (6031464750847/156250000000 : ℝ)*(major1) + (1930068720271041/50000000000000 : ℝ)*(major2) + (16355223581/100000000000000 : ℝ)*(sp1) + (15008812999/25000000000000 : ℝ)*(sp2) + (16912491111/100000000000000 : ℝ)*(sp3) + (1283509220388621/25000000000000 : ℝ)*(sp4) + (1283511605522071/25000000000000 : ℝ)*(sp5) + (5134002742059869/100000000000000 : ℝ)*(sp6) + (162933495583217/6250000000000 : ℝ)*(sp7) + (12947878691/50000000000000 : ℝ)*(sp12) + (2606952841822583/100000000000000 : ℝ)*(f.failure) + (1026812555462373/20000000000000 : ℝ)*(f.sum) + (6128264040433/1373500000000000000000000000 : ℝ)*base65 + (71393398118058933/4292187500000000000000000000000 : ℝ)*base68 + (1270573384069367049/1373500000000000000000000000000000 : ℝ)*base70 + (22291012478427241/8584375000000000000000000000000 : ℝ)*base72 + (6726274612321/1373500000000000000000000000 : ℝ)*base74 + (13026791232142132951/1373500000000000000000000000000000 : ℝ)*base75 + (23560637918349779/2146093750000000000000000000000 : ℝ)*base78 + (87192448548264741/8584375000000000000000000000000 : ℝ)*base80 + (11170723233979/2747000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (74293107/5000000000000000000000 : ℝ)*base89 + (74293107/5000000000000000000000 : ℝ)*base91 + (25706893/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (14811/25000 : ℝ) ≤ (162749501081980317473655507/274700000000000000000000000 : ℝ) := by norm_num
    linear_combination (2511079/12500000000000 : ℝ)*(upper0) + (84663/2500000000000 : ℝ)*(lower1) + (26186201/50000000000000 : ℝ)*(upper4) + (490386698150579/12500000000000 : ℝ)*(major0) + (490386698150579/12500000000000 : ℝ)*(major1) + (490386698150579/12500000000000 : ℝ)*(major2) + (517695467519833/10000000000000 : ℝ)*(sp0) + (323559428035323/6250000000000 : ℝ)*(sp1) + (1035393179035979/20000000000000 : ℝ)*(sp2) + (165591166266697/6250000000000 : ℝ)*(sp3) + (8572120747/50000000000000 : ℝ)*(sp5) + (2097626767/100000000000000 : ℝ)*(sp6) + (294024631/2500000000000 : ℝ)*(sp7) + (13317608333/100000000000000 : ℝ)*(sp8) + (331183802656549/12500000000000 : ℝ)*(f.failure) + (2588483996403331/50000000000000 : ℝ)*(f.sum) + (4587452007497/2747000000000000000000000000 : ℝ)*base65 + (2725446464341734869/343375000000000000000000000000000 : ℝ)*base67 + (4930159814074890131/343375000000000000000000000000000 : ℝ)*base70 + (1223512241986265131/343375000000000000000000000000000 : ℝ)*base72 + (18974673536923/1373500000000000000000000000 : ℝ)*base74 + (9671576701265131/343375000000000000000000000000000 : ℝ)*base76 + (946427525516734869/343375000000000000000000000000000 : ℝ)*base77 + (9052074410467734869/343375000000000000000000000000000 : ℝ)*base79 + (282879649129/1373500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (5125479/625000000000000000000 : ℝ)*base90 + (5125479/625000000000000000000 : ℝ)*base92 + (5125479/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (15917/20000 : ℝ) ≤ (273283096561150725135866174553099/343375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (743065809/100000000000000 : ℝ)*(upper0) + (276962927/100000000000000 : ℝ)*(upper2) + (39610081/25000000000000 : ℝ)*(lower3) + (111131633/10000000000000 : ℝ)*(lower5) + (4391274325651329/100000000000000 : ℝ)*(major0) + (4391274325651329/100000000000000 : ℝ)*(major1) + (439127432565133/10000000000000 : ℝ)*(major2) + (381054501273/100000000000000 : ℝ)*(sp1) + (32838699461/20000000000000 : ℝ)*(sp3) + (3156525027/100000000000000 : ℝ)*(sp4) + (5790358996381961/100000000000000 : ℝ)*(sp8) + (1447495274601429/25000000000000 : ℝ)*(sp9) + (5790362152906989/100000000000000 : ℝ)*(sp10) + (148274659248989/5000000000000 : ℝ)*(sp11) + (1482828689238543/50000000000000 : ℝ)*(f.failure) + (5790362152906989/100000000000000 : ℝ)*(f.sum) + (5886427548501/2747000000000000000000000000 : ℝ)*base65 + (21222451976627368119/2747000000000000000000000000000000 : ℝ)*base67 + (5437577493803585963/274700000000000000000000000000000 : ℝ)*base69 + (21898549841329368119/2747000000000000000000000000000000 : ℝ)*base71 + (549828662829/137350000000000000000000000 : ℝ)*base74 + (3451497330539785963/274700000000000000000000000000000 : ℝ)*base75 + (22618354358304368119/2747000000000000000000000000000000 : ℝ)*base77 + (80860093595071368119/2747000000000000000000000000000000 : ℝ)*base79 + (6530053844177/1373500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (10660053/2500000000000000000000 : ℝ)*base90 + (10660053/2500000000000000000000 : ℝ)*base92 + (35660053/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-41481/50000 : ℝ) ≤ (-569721478285661031442558281/686750000000000000000000000 : ℝ) := by norm_num
    linear_combination (43941149/100000000000000 : ℝ)*(lower0) + (108070643/50000000000000 : ℝ)*(lower1) + (90691441/100000000000000 : ℝ)*(lower2) + (60256059/50000000000000 : ℝ)*(lower4) + (4425887254592893/100000000000000 : ℝ)*(major0) + (4425887254592893/100000000000000 : ℝ)*(major1) + (4425887254592893/100000000000000 : ℝ)*(major2) + (387584303/4000000000000 : ℝ)*(sp0) + (354707406977/100000000000000 : ℝ)*(sp5) + (15950870033/3125000000000 : ℝ)*(sp6) + (1472596136284837/25000000000000 : ℝ)*(sp12) + (1178007905467989/20000000000000 : ℝ)*(sp13) + (5889883806905867/100000000000000 : ℝ)*(sp14) + (1494516650465041/50000000000000 : ℝ)*(sp15) + (1494516650465041/50000000000000 : ℝ)*(f.failure) + (5890394234746923/100000000000000 : ℝ)*(f.sum) + (7550859344073/109880000000000000000000000 : ℝ)*base65 + (26418846297498568677/2747000000000000000000000000000000 : ℝ)*base68 + (20807368282294568677/2747000000000000000000000000000000 : ℝ)*base70 + (94164495148992431323/2747000000000000000000000000000000 : ℝ)*base71 + (4460030358447/686750000000000000000000000 : ℝ)*base74 + (1481353016212568677/2747000000000000000000000000000000 : ℝ)*base76 + (8364958188161431323/2747000000000000000000000000000000 : ℝ)*base77 + (3224530749899431323/2747000000000000000000000000000000 : ℝ)*base79 + (461502641459/686750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (34937589/2500000000000000000000 : ℝ)*base89 + (34937589/2500000000000000000000 : ℝ)*base91 + (34937589/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1070_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74035429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2801/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5629/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(14811/25000 : ℝ) else (15917/20000 : ℝ) ≤ X j i ∧ X j i ≤ (41481/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1070_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1070_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74035429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2801/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11257/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(14811/25000 : ℝ) else (15917/20000 : ℝ) ≤ X j i ∧ X j i ≤ (41481/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1070_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1070_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74035429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2801/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11257/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(14811/25000 : ℝ) else (15917/20000 : ℝ) ≤ X j i ∧ X j i ≤ (41481/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1070_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

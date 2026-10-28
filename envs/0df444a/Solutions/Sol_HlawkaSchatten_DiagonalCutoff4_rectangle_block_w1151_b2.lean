-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1151_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:36:06.554548+00:00
-- url     : https://prove2.me/submissions/cdace15c-42b8-414d-9eb6-b89603131782

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
theorem support_rectangle_w1151_s6_0 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2162559873/10000000000 : ℝ)*x 0 + (269660253/500000000 : ℝ)*x 1 + (2632784713/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2162559873/10000000000 : ℝ)^1043 ≤ (105131447253/800000000000 : ℝ)^787 := by
    have hnat : (2162559873 : ℕ)^1043*800000000000^787 ≤ 105131447253^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162559873 10000000000 105131447253 800000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269660253/500000000 : ℝ)^1043 ≤ (44118478108883/100000000000000 : ℝ)^787 := by
    have hnat : (269660253 : ℕ)^1043*100000000000000^787 ≤ 44118478108883^787*500000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269660253 500000000 44118478108883 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632784713/5000000000 : ℝ)^1043 ≤ (8548018194457/20000000000000 : ℝ)^787 := by
    have hnat : (2632784713 : ℕ)^1043*20000000000000^787 ≤ 8548018194457^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632784713 5000000000 8548018194457 20000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2162559873/10000000000 : ℝ), (269660253/500000000 : ℝ), (2632784713/5000000000 : ℝ)] ![(105131447253/800000000000 : ℝ), (44118478108883/100000000000000 : ℝ), (8548018194457/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2162559873/10000000000 : ℝ)|^1043 ≤ (105131447253/800000000000 : ℝ)^787
        have hw : |(-2162559873/10000000000 : ℝ)|=(2162559873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269660253/500000000 : ℝ)|^1043 ≤ (44118478108883/100000000000000 : ℝ)^787
        have hw : |(269660253/500000000 : ℝ)|=(269660253/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632784713/5000000000 : ℝ)|^1043 ≤ (8548018194457/20000000000000 : ℝ)^787
        have hw : |(2632784713/5000000000 : ℝ)|=(2632784713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s6_1 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (668101067/1250000000 : ℝ)*x 0 + (-1113650641/5000000000 : ℝ)*x 1 + (2632784713/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668101067/1250000000 : ℝ)^1043 ≤ (43594562018661/100000000000000 : ℝ)^787 := by
    have hnat : (668101067 : ℕ)^1043*100000000000000^787 ≤ 43594562018661^787*1250000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668101067 1250000000 43594562018661 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1113650641/5000000000 : ℝ)^1043 ≤ (6832673499863/50000000000000 : ℝ)^787 := by
    have hnat : (1113650641 : ℕ)^1043*50000000000000^787 ≤ 6832673499863^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1113650641 5000000000 6832673499863 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632784713/5000000000 : ℝ)^1043 ≤ (8548018194457/20000000000000 : ℝ)^787 := by
    have hnat : (2632784713 : ℕ)^1043*20000000000000^787 ≤ 8548018194457^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632784713 5000000000 8548018194457 20000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668101067/1250000000 : ℝ), (-1113650641/5000000000 : ℝ), (2632784713/5000000000 : ℝ)] ![(43594562018661/100000000000000 : ℝ), (6832673499863/50000000000000 : ℝ), (8548018194457/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668101067/1250000000 : ℝ)|^1043 ≤ (43594562018661/100000000000000 : ℝ)^787
        have hw : |(668101067/1250000000 : ℝ)|=(668101067/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1113650641/5000000000 : ℝ)|^1043 ≤ (6832673499863/50000000000000 : ℝ)^787
        have hw : |(-1113650641/5000000000 : ℝ)|=(1113650641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632784713/5000000000 : ℝ)|^1043 ≤ (8548018194457/20000000000000 : ℝ)^787
        have hw : |(2632784713/5000000000 : ℝ)|=(2632784713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s6_2 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2672404267/5000000000 : ℝ)*x 0 + (210622777/400000000 : ℝ)*x 1 + (-556825321/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672404267/5000000000 : ℝ)^1043 ≤ (21797280998521/50000000000000 : ℝ)^787 := by
    have hnat : (2672404267 : ℕ)^1043*50000000000000^787 ≤ 21797280998521^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672404267 5000000000 21797280998521 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210622777/400000000 : ℝ)^1043 ≤ (5342511370191/12500000000000 : ℝ)^787 := by
    have hnat : (210622777 : ℕ)^1043*12500000000000^787 ≤ 5342511370191^787*400000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210622777 400000000 5342511370191 12500000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (556825321/2500000000 : ℝ)^1043 ≤ (3416336753997/25000000000000 : ℝ)^787 := by
    have hnat : (556825321 : ℕ)^1043*25000000000000^787 ≤ 3416336753997^787*2500000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      556825321 2500000000 3416336753997 25000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672404267/5000000000 : ℝ), (210622777/400000000 : ℝ), (-556825321/2500000000 : ℝ)] ![(21797280998521/50000000000000 : ℝ), (5342511370191/12500000000000 : ℝ), (3416336753997/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672404267/5000000000 : ℝ)|^1043 ≤ (21797280998521/50000000000000 : ℝ)^787
        have hw : |(2672404267/5000000000 : ℝ)|=(2672404267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210622777/400000000 : ℝ)|^1043 ≤ (5342511370191/12500000000000 : ℝ)^787
        have hw : |(210622777/400000000 : ℝ)|=(210622777/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-556825321/2500000000 : ℝ)|^1043 ≤ (3416336753997/25000000000000 : ℝ)^787
        have hw : |(-556825321/2500000000 : ℝ)|=(556825321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s6_3 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (218169513/500000000 : ℝ)*x 0 + (42380429/100000000 : ℝ)*x 1 + (2246209519/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218169513/500000000 : ℝ)^1043 ≤ (16658423861989/50000000000000 : ℝ)^787 := by
    have hnat : (218169513 : ℕ)^1043*50000000000000^787 ≤ 16658423861989^787*500000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218169513 500000000 16658423861989 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42380429/100000000 : ℝ)^1043 ≤ (1282175536243/4000000000000 : ℝ)^787 := by
    have hnat : (42380429 : ℕ)^1043*4000000000000^787 ≤ 1282175536243^787*100000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42380429 100000000 1282175536243 4000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2246209519/5000000000 : ℝ)^1043 ≤ (541074435223/1562500000000 : ℝ)^787 := by
    have hnat : (2246209519 : ℕ)^1043*1562500000000^787 ≤ 541074435223^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246209519 5000000000 541074435223 1562500000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218169513/500000000 : ℝ), (42380429/100000000 : ℝ), (2246209519/5000000000 : ℝ)] ![(16658423861989/50000000000000 : ℝ), (1282175536243/4000000000000 : ℝ), (541074435223/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218169513/500000000 : ℝ)|^1043 ≤ (16658423861989/50000000000000 : ℝ)^787
        have hw : |(218169513/500000000 : ℝ)|=(218169513/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42380429/100000000 : ℝ)|^1043 ≤ (1282175536243/4000000000000 : ℝ)^787
        have hw : |(42380429/100000000 : ℝ)|=(42380429/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2246209519/5000000000 : ℝ)|^1043 ≤ (541074435223/1562500000000 : ℝ)^787
        have hw : |(2246209519/5000000000 : ℝ)|=(2246209519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s6_4 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1081282429/5000000000 : ℝ)*x 0 + (658236481/1250000000 : ℝ)*x 1 + (539288143/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081282429/5000000000 : ℝ)^1043 ≤ (2628294210657/20000000000000 : ℝ)^787 := by
    have hnat : (1081282429 : ℕ)^1043*20000000000000^787 ≤ 2628294210657^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081282429 5000000000 2628294210657 20000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658236481/1250000000 : ℝ)^1043 ≤ (42743559368213/100000000000000 : ℝ)^787 := by
    have hnat : (658236481 : ℕ)^1043*100000000000000^787 ≤ 42743559368213^787*1250000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658236481 1250000000 42743559368213 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539288143/1000000000 : ℝ)^1043 ≤ (44114969558639/100000000000000 : ℝ)^787 := by
    have hnat : (539288143 : ℕ)^1043*100000000000000^787 ≤ 44114969558639^787*1000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539288143 1000000000 44114969558639 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1081282429/5000000000 : ℝ), (658236481/1250000000 : ℝ), (539288143/1000000000 : ℝ)] ![(2628294210657/20000000000000 : ℝ), (42743559368213/100000000000000 : ℝ), (44114969558639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1081282429/5000000000 : ℝ)|^1043 ≤ (2628294210657/20000000000000 : ℝ)^787
        have hw : |(-1081282429/5000000000 : ℝ)|=(1081282429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658236481/1250000000 : ℝ)|^1043 ≤ (42743559368213/100000000000000 : ℝ)^787
        have hw : |(658236481/1250000000 : ℝ)|=(658236481/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539288143/1000000000 : ℝ)|^1043 ≤ (44114969558639/100000000000000 : ℝ)^787
        have hw : |(539288143/1000000000 : ℝ)|=(539288143/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s6_5 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312450003/10000000000 : ℝ)*x 0 + (-32812331/156250000 : ℝ)*x 1 + (1348220379/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312450003/10000000000 : ℝ)^1043 ≤ (43245124016367/100000000000000 : ℝ)^787 := by
    have hnat : (5312450003 : ℕ)^1043*100000000000000^787 ≤ 43245124016367^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312450003 10000000000 43245124016367 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32812331/156250000 : ℝ)^1043 ≤ (1579988185279/12500000000000 : ℝ)^787 := by
    have hnat : (32812331 : ℕ)^1043*12500000000000^787 ≤ 1579988185279^787*156250000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32812331 156250000 1579988185279 12500000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348220379/2500000000 : ℝ)^1043 ≤ (44114970490977/100000000000000 : ℝ)^787 := by
    have hnat : (1348220379 : ℕ)^1043*100000000000000^787 ≤ 44114970490977^787*2500000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348220379 2500000000 44114970490977 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312450003/10000000000 : ℝ), (-32812331/156250000 : ℝ), (1348220379/2500000000 : ℝ)] ![(43245124016367/100000000000000 : ℝ), (1579988185279/12500000000000 : ℝ), (44114970490977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312450003/10000000000 : ℝ)|^1043 ≤ (43245124016367/100000000000000 : ℝ)^787
        have hw : |(5312450003/10000000000 : ℝ)|=(5312450003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-32812331/156250000 : ℝ)|^1043 ≤ (1579988185279/12500000000000 : ℝ)^787
        have hw : |(-32812331/156250000 : ℝ)|=(32812331/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348220379/2500000000 : ℝ)|^1043 ≤ (44114970490977/100000000000000 : ℝ)^787
        have hw : |(1348220379/2500000000 : ℝ)|=(1348220379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s6_6 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1328112497/2500000000 : ℝ)*x 0 + (84263773/156250000 : ℝ)*x 1 + (-2099989263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328112497/2500000000 : ℝ)^1043 ≤ (43245123854543/100000000000000 : ℝ)^787 := by
    have hnat : (1328112497 : ℕ)^1043*100000000000000^787 ≤ 43245123854543^787*2500000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328112497 2500000000 43245123854543 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84263773/156250000 : ℝ)^1043 ≤ (44114970013967/100000000000000 : ℝ)^787 := by
    have hnat : (84263773 : ℕ)^1043*100000000000000^787 ≤ 44114970013967^787*156250000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84263773 156250000 44114970013967 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2099989263/10000000000 : ℝ)^1043 ≤ (1263990611241/10000000000000 : ℝ)^787 := by
    have hnat : (2099989263 : ℕ)^1043*10000000000000^787 ≤ 1263990611241^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099989263 10000000000 1263990611241 10000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328112497/2500000000 : ℝ), (84263773/156250000 : ℝ), (-2099989263/10000000000 : ℝ)] ![(43245123854543/100000000000000 : ℝ), (44114970013967/100000000000000 : ℝ), (1263990611241/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328112497/2500000000 : ℝ)|^1043 ≤ (43245123854543/100000000000000 : ℝ)^787
        have hw : |(1328112497/2500000000 : ℝ)|=(1328112497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84263773/156250000 : ℝ)|^1043 ≤ (44114970013967/100000000000000 : ℝ)^787
        have hw : |(84263773/156250000 : ℝ)|=(84263773/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2099989263/10000000000 : ℝ)|^1043 ≤ (1263990611241/10000000000000 : ℝ)^787
        have hw : |(-2099989263/10000000000 : ℝ)|=(2099989263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s6_7 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4363400179/10000000000 : ℝ)*x 0 + (2245888219/5000000000 : ℝ)*x 1 + (1059671939/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363400179/10000000000 : ℝ)^1043 ≤ (33316948097109/100000000000000 : ℝ)^787 := by
    have hnat : (4363400179 : ℕ)^1043*100000000000000^787 ≤ 33316948097109^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363400179 10000000000 33316948097109 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2245888219/5000000000 : ℝ)^1043 ≤ (8655549856441/25000000000000 : ℝ)^787 := by
    have hnat : (2245888219 : ℕ)^1043*25000000000000^787 ≤ 8655549856441^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245888219 5000000000 8655549856441 25000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1059671939/2500000000 : ℝ)^1043 ≤ (2003803278977/6250000000000 : ℝ)^787 := by
    have hnat : (1059671939 : ℕ)^1043*6250000000000^787 ≤ 2003803278977^787*2500000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059671939 2500000000 2003803278977 6250000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363400179/10000000000 : ℝ), (2245888219/5000000000 : ℝ), (1059671939/2500000000 : ℝ)] ![(33316948097109/100000000000000 : ℝ), (8655549856441/25000000000000 : ℝ), (2003803278977/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363400179/10000000000 : ℝ)|^1043 ≤ (33316948097109/100000000000000 : ℝ)^787
        have hw : |(4363400179/10000000000 : ℝ)|=(4363400179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2245888219/5000000000 : ℝ)|^1043 ≤ (8655549856441/25000000000000 : ℝ)^787
        have hw : |(2245888219/5000000000 : ℝ)|=(2245888219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1059671939/2500000000 : ℝ)|^1043 ≤ (2003803278977/6250000000000 : ℝ)^787
        have hw : |(1059671939/2500000000 : ℝ)|=(1059671939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1151_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7482467/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (354/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (5679/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7031/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14093/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (354/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14093/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (354/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14093/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (354/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14093/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (354/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14093/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (354/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14093/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (354/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (354/3125 : ℝ) ^ (8343/2048 : ℝ) ≤ (2804821527774513/20000000000000000000 : ℝ) := by
    have hpowers : (354/3125 : ℝ)^8343 ≤ (2804821527774513/20000000000000000000 : ℝ)^2048 := by
      have hnat : (354 : ℕ)^8343*20000000000000000000^2048 ≤ 2804821527774513^2048*3125^8343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        354 3125 2804821527774513 20000000000000000000 8343 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (354/3125 : ℝ)) (X := (2804821527774513/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14093/100000 : ℝ) ^ (8343/2048 : ℝ) ≤ (34140465104007357/100000000000000000000 : ℝ) := by
    have hpowers : (14093/100000 : ℝ)^8343 ≤ (34140465104007357/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14093 : ℕ)^8343*100000000000000000000^2048 ≤ 34140465104007357^2048*100000^8343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14093 100000 34140465104007357 100000000000000000000 8343 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14093/100000 : ℝ)) (X := (34140465104007357/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002804821527774513/10000000000000000000 : ℝ) ≤ (2500172110354671/2500000000000000 : ℝ) ^ (8343/2048 : ℝ) := by
    have hpowers : (10002804821527774513/10000000000000000000 : ℝ)^2048 ≤ (2500172110354671/2500000000000000 : ℝ)^8343 := by
      have hnat : (10002804821527774513 : ℕ)^2048*2500000000000000^8343 ≤ 2500172110354671^8343*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002804821527774513 10000000000000000000 2500172110354671 2500000000000000 2048 8343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500172110354671/2500000000000000 : ℝ)) (X := (10002804821527774513/10000000000000000000 : ℝ)) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024082286371439961/50000000000000000000 : ℝ) ≤ (10001182106272023/10000000000000000 : ℝ) ^ (8343/2048 : ℝ) := by
    have hpowers : (50024082286371439961/50000000000000000000 : ℝ)^2048 ≤ (10001182106272023/10000000000000000 : ℝ)^8343 := by
      have hnat : (50024082286371439961 : ℕ)^2048*10000000000000000^8343 ≤ 10001182106272023^8343*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024082286371439961 50000000000000000000 10001182106272023 10000000000000000 2048 8343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001182106272023/10000000000000000 : ℝ)) (X := (50024082286371439961/50000000000000000000 : ℝ)) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034140465104007357/50000000000000000000 : ℝ) ≤ (5000837885562681/5000000000000000 : ℝ) ^ (8343/2048 : ℝ) := by
    have hpowers : (50034140465104007357/50000000000000000000 : ℝ)^2048 ≤ (5000837885562681/5000000000000000 : ℝ)^8343 := by
      have hnat : (50034140465104007357 : ℕ)^2048*5000000000000000^8343 ≤ 5000837885562681^8343*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034140465104007357 50000000000000000000 5000837885562681 5000000000000000 2048 8343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000837885562681/5000000000000000 : ℝ)) (X := (50034140465104007357/50000000000000000000 : ℝ)) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2804821527774513/20000000000000000000 : ℝ) ≤ ((987168538200193317/987500000000000000 : ℝ)+2*(70523550477/39500000000000 : ℝ)*(354/3125 : ℝ))^(8343/2048 : ℝ) := by
    rw [show (987168538200193317/987500000000000000 : ℝ)+2*(70523550477/39500000000000 : ℝ)*(354/3125 : ℝ)=(2500172110354671/2500000000000000 : ℝ) by norm_num, show 1+2*(2804821527774513/20000000000000000000 : ℝ)=(10002804821527774513/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34140465104007357/100000000000000000000 : ℝ)+(2804821527774513/20000000000000000000 : ℝ) ≤ ((987168538200193317/987500000000000000 : ℝ)+(70523550477/39500000000000 : ℝ)*((14093/100000 : ℝ)+(354/3125 : ℝ)))^(8343/2048 : ℝ) := by
    rw [show (987168538200193317/987500000000000000 : ℝ)+(70523550477/39500000000000 : ℝ)*((14093/100000 : ℝ)+(354/3125 : ℝ))=(10001182106272023/10000000000000000 : ℝ) by norm_num, show 1+(34140465104007357/100000000000000000000 : ℝ)+(2804821527774513/20000000000000000000 : ℝ)=(50024082286371439961/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34140465104007357/100000000000000000000 : ℝ) ≤ ((987168538200193317/987500000000000000 : ℝ)+2*(70523550477/39500000000000 : ℝ)*(14093/100000 : ℝ))^(8343/2048 : ℝ) := by
    rw [show (987168538200193317/987500000000000000 : ℝ)+2*(70523550477/39500000000000 : ℝ)*(14093/100000 : ℝ)=(5000837885562681/5000000000000000 : ℝ) by norm_num, show 1+2*(34140465104007357/100000000000000000000 : ℝ)=(50034140465104007357/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (987168538200193317/987500000000000000 : ℝ)*(X 1 0+X 2 0)+(70523550477/39500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8343/2048 : ℝ)) (lo := (354/3125 : ℝ)) (hi := (14093/100000 : ℝ)) (c := (987168538200193317/987500000000000000 : ℝ)) (alpha := (70523550477/39500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (987168538200193317/987500000000000000 : ℝ)*(X 0 1+X 2 1)+(70523550477/39500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8343/2048 : ℝ)) (lo := (354/3125 : ℝ)) (hi := (14093/100000 : ℝ)) (c := (987168538200193317/987500000000000000 : ℝ)) (alpha := (70523550477/39500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (987168538200193317/987500000000000000 : ℝ)*(X 0 2+X 1 2)+(70523550477/39500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8343/2048 : ℝ)) (lo := (354/3125 : ℝ)) (hi := (14093/100000 : ℝ)) (c := (987168538200193317/987500000000000000 : ℝ)) (alpha := (70523550477/39500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2162559873/10000000000 : ℝ)*X 0 0+(269660253/500000000 : ℝ)*X 0 1+(2632784713/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668101067/1250000000 : ℝ)*X 1 0+(-1113650641/5000000000 : ℝ)*X 1 1+(2632784713/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672404267/5000000000 : ℝ)*X 2 0+(210622777/400000000 : ℝ)*X 2 1+(-556825321/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((218169513/500000000 : ℝ)*X 0 0+(42380429/100000000 : ℝ)*X 0 1+(2246209519/5000000000 : ℝ)*X 0 2+(218169513/500000000 : ℝ)*X 1 0+(42380429/100000000 : ℝ)*X 1 1+(2246209519/5000000000 : ℝ)*X 1 2+(218169513/500000000 : ℝ)*X 2 0+(42380429/100000000 : ℝ)*X 2 1+(2246209519/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1081282429/5000000000 : ℝ)*X 0 0+(658236481/1250000000 : ℝ)*X 0 1+(539288143/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312450003/10000000000 : ℝ)*X 1 0+(-32812331/156250000 : ℝ)*X 1 1+(1348220379/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328112497/2500000000 : ℝ)*X 2 0+(84263773/156250000 : ℝ)*X 2 1+(-2099989263/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4363400179/10000000000 : ℝ)*X 0 0+(2245888219/5000000000 : ℝ)*X 0 1+(1059671939/2500000000 : ℝ)*X 0 2+(4363400179/10000000000 : ℝ)*X 1 0+(2245888219/5000000000 : ℝ)*X 1 1+(1059671939/2500000000 : ℝ)*X 1 2+(4363400179/10000000000 : ℝ)*X 2 0+(2245888219/5000000000 : ℝ)*X 2 1+(1059671939/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (152139241755012446518435641/24687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1216977431/100000000000000 : ℝ)*(base19) + (282220233/25000000000000 : ℝ)*(base23) + (45518917/100000000000000 : ℝ)*(lower2) + (3161311/2000000000000 : ℝ)*(upper3) + (89940141/100000000000000 : ℝ)*(upper5) + (5883045372627691/100000000000000 : ℝ)*(major0) + (5883045372627691/100000000000000 : ℝ)*(major1) + (5883045372627691/100000000000000 : ℝ)*(major2) + (7834837305571597/100000000000000 : ℝ)*(sp0) + (1566973785897027/20000000000000 : ℝ)*(sp1) + (3917434508790817/50000000000000 : ℝ)*(sp2) + (1965601200338687/50000000000000 : ℝ)*(sp3) + (32840890969/100000000000000 : ℝ)*(sp4) + (3598539071/20000000000000 : ℝ)*(sp7) + (491402549171591/12500000000000 : ℝ)*(f.failure) + (3917435073231283/50000000000000 : ℝ)*(f.sum) + (1148957834657/1975000000000000000000000000 : ℝ)*base65 + (1165679414739983953/98750000000000000000000000000000 : ℝ)*base68 + (3123805702237483953/98750000000000000000000000000000 : ℝ)*base70 + (190655141113766047/98750000000000000000000000000000 : ℝ)*base71 + (16908853905893/1975000000000000000000000000 : ℝ)*base74 + (4583872199639983953/98750000000000000000000000000000 : ℝ)*base76 + (975755388241233953/98750000000000000000000000000000 : ℝ)*base78 + (2309731632892483953/98750000000000000000000000000000 : ℝ)*base80 + (2609961574993/1975000000000000000000000000 : ℝ)*base82 + (119997/62500000000000000000 : ℝ)*base89 + (119997/62500000000000000000 : ℝ)*base91 + (119997/62500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (249455932972284391916173791/24687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2002861021/100000000000000 : ℝ)*(base19) + (2107727413/100000000000000 : ℝ)*(base23) + (129217561/50000000000000 : ℝ)*(upper3) + (67601399/100000000000000 : ℝ)*(lower4) + (43875567/20000000000000 : ℝ)*(upper5) + (5912921020235841/100000000000000 : ℝ)*(major0) + (5912921020235841/100000000000000 : ℝ)*(major1) + (5912921020235841/100000000000000 : ℝ)*(major2) + (57498760309/100000000000000 : ℝ)*(sp1) + (57474116129/100000000000000 : ℝ)*(sp2) + (7874657541908591/100000000000000 : ℝ)*(sp4) + (3937299020143631/50000000000000 : ℝ)*(sp5) + (157491959201301/2000000000000 : ℝ)*(sp6) + (246949010109059/6250000000000 : ℝ)*(sp7) + (246949010109059/6250000000000 : ℝ)*(f.failure) + (7874657541908591/100000000000000 : ℝ)*(f.sum) + (6181465502393/1975000000000000000000000000 : ℝ)*base66 + (29805998164000403/98750000000000000000000000000000 : ℝ)*base68 + (1341587080378499597/98750000000000000000000000000000 : ℝ)*base69 + (1115819861831500403/98750000000000000000000000000000 : ℝ)*base72 + (9878465772307/1975000000000000000000000000 : ℝ)*base73 + (374825843351500403/98750000000000000000000000000000 : ℝ)*base76 + (290665343336500403/98750000000000000000000000000000 : ℝ)*base78 + (3398508519792750403/98750000000000000000000000000000 : ℝ)*base80 + (529015737107/1975000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (56053/31250000000000000000 : ℝ)*base89 + (56053/31250000000000000000 : ℝ)*base91 + (56053/31250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1151_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7482467/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (354/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5679/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1151_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1151_s7_0 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-135161581/625000000 : ℝ)*x 0 + (215715867/400000000 : ℝ)*x 1 + (82279081/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135161581/625000000 : ℝ)^1043 ≤ (6570817825439/50000000000000 : ℝ)^787 := by
    have hnat : (135161581 : ℕ)^1043*50000000000000^787 ≤ 6570817825439^787*625000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135161581 625000000 6570817825439 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215715867/400000000 : ℝ)^1043 ≤ (22057567415897/50000000000000 : ℝ)^787 := by
    have hnat : (215715867 : ℕ)^1043*50000000000000^787 ≤ 22057567415897^787*400000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215715867 400000000 22057567415897 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82279081/156250000 : ℝ)^1043 ≤ (42743229502847/100000000000000 : ℝ)^787 := by
    have hnat : (82279081 : ℕ)^1043*100000000000000^787 ≤ 42743229502847^787*156250000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82279081 156250000 42743229502847 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-135161581/625000000 : ℝ), (215715867/400000000 : ℝ), (82279081/156250000 : ℝ)] ![(6570817825439/50000000000000 : ℝ), (22057567415897/50000000000000 : ℝ), (42743229502847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-135161581/625000000 : ℝ)|^1043 ≤ (6570817825439/50000000000000 : ℝ)^787
        have hw : |(-135161581/625000000 : ℝ)|=(135161581/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215715867/400000000 : ℝ)|^1043 ≤ (22057567415897/50000000000000 : ℝ)^787
        have hw : |(215715867/400000000 : ℝ)|=(215715867/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(82279081/156250000 : ℝ)|^1043 ≤ (42743229502847/100000000000000 : ℝ)^787
        have hw : |(82279081/156250000 : ℝ)|=(82279081/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s7_1 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (534473129/1000000000 : ℝ)*x 0 + (-2227017971/10000000000 : ℝ)*x 1 + (5265861189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534473129/1000000000 : ℝ)^1043 ≤ (43593727022033/100000000000000 : ℝ)^787 := by
    have hnat : (534473129 : ℕ)^1043*100000000000000^787 ≤ 43593727022033^787*1000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534473129 1000000000 43593727022033 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2227017971/10000000000 : ℝ)^1043 ≤ (13663043406859/100000000000000 : ℝ)^787 := by
    have hnat : (2227017971 : ℕ)^1043*100000000000000^787 ≤ 13663043406859^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2227017971 10000000000 13663043406859 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265861189/10000000000 : ℝ)^1043 ≤ (21371614778317/50000000000000 : ℝ)^787 := by
    have hnat : (5265861189 : ℕ)^1043*50000000000000^787 ≤ 21371614778317^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265861189 10000000000 21371614778317 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534473129/1000000000 : ℝ), (-2227017971/10000000000 : ℝ), (5265861189/10000000000 : ℝ)] ![(43593727022033/100000000000000 : ℝ), (13663043406859/100000000000000 : ℝ), (21371614778317/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534473129/1000000000 : ℝ)|^1043 ≤ (43593727022033/100000000000000 : ℝ)^787
        have hw : |(534473129/1000000000 : ℝ)|=(534473129/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2227017971/10000000000 : ℝ)|^1043 ≤ (13663043406859/100000000000000 : ℝ)^787
        have hw : |(-2227017971/10000000000 : ℝ)|=(2227017971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265861189/10000000000 : ℝ)|^1043 ≤ (21371614778317/50000000000000 : ℝ)^787
        have hw : |(5265861189/10000000000 : ℝ)|=(5265861189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s7_2 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1336182823/2500000000 : ℝ)*x 0 + (526586119/1000000000 : ℝ)*x 1 + (-2227017967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336182823/2500000000 : ℝ)^1043 ≤ (10898431760913/25000000000000 : ℝ)^787 := by
    have hnat : (1336182823 : ℕ)^1043*25000000000000^787 ≤ 10898431760913^787*2500000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336182823 2500000000 10898431760913 25000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526586119/1000000000 : ℝ)^1043 ≤ (42743229567391/100000000000000 : ℝ)^787 := by
    have hnat : (526586119 : ℕ)^1043*100000000000000^787 ≤ 42743229567391^787*1000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526586119 1000000000 42743229567391 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2227017967/10000000000 : ℝ)^1043 ≤ (53371263181/390625000000 : ℝ)^787 := by
    have hnat : (2227017967 : ℕ)^1043*390625000000^787 ≤ 53371263181^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2227017967 10000000000 53371263181 390625000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336182823/2500000000 : ℝ), (526586119/1000000000 : ℝ), (-2227017967/10000000000 : ℝ)] ![(10898431760913/25000000000000 : ℝ), (42743229567391/100000000000000 : ℝ), (53371263181/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336182823/2500000000 : ℝ)|^1043 ≤ (10898431760913/25000000000000 : ℝ)^787
        have hw : |(1336182823/2500000000 : ℝ)|=(1336182823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526586119/1000000000 : ℝ)|^1043 ≤ (42743229567391/100000000000000 : ℝ)^787
        have hw : |(526586119/1000000000 : ℝ)|=(526586119/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2227017967/10000000000 : ℝ)|^1043 ≤ (53371263181/390625000000 : ℝ)^787
        have hw : |(-2227017967/10000000000 : ℝ)|=(2227017967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s7_3 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4363405537/10000000000 : ℝ)*x 0 + (2119319487/5000000000 : ℝ)*x 1 + (4491819001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363405537/10000000000 : ℝ)^1043 ≤ (33317002316239/100000000000000 : ℝ)^787 := by
    have hnat : (4363405537 : ℕ)^1043*100000000000000^787 ≤ 33317002316239^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363405537 10000000000 33317002316239 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2119319487/5000000000 : ℝ)^1043 ≤ (32060363460089/100000000000000 : ℝ)^787 := by
    have hnat : (2119319487 : ℕ)^1043*100000000000000^787 ≤ 32060363460089^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119319487 5000000000 32060363460089 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4491819001/10000000000 : ℝ)^1043 ≤ (17311317107607/50000000000000 : ℝ)^787 := by
    have hnat : (4491819001 : ℕ)^1043*50000000000000^787 ≤ 17311317107607^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491819001 10000000000 17311317107607 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363405537/10000000000 : ℝ), (2119319487/5000000000 : ℝ), (4491819001/10000000000 : ℝ)] ![(33317002316239/100000000000000 : ℝ), (32060363460089/100000000000000 : ℝ), (17311317107607/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363405537/10000000000 : ℝ)|^1043 ≤ (33317002316239/100000000000000 : ℝ)^787
        have hw : |(4363405537/10000000000 : ℝ)|=(4363405537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2119319487/5000000000 : ℝ)|^1043 ≤ (32060363460089/100000000000000 : ℝ)^787
        have hw : |(2119319487/5000000000 : ℝ)|=(2119319487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4491819001/10000000000 : ℝ)|^1043 ≤ (17311317107607/50000000000000 : ℝ)^787
        have hw : |(4491819001/10000000000 : ℝ)|=(4491819001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s7_4 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2162590143/10000000000 : ℝ)*x 0 + (2633090293/5000000000 : ℝ)*x 1 + (5392576133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2162590143/10000000000 : ℝ)^1043 ≤ (410677333947/3125000000000 : ℝ)^787 := by
    have hnat : (2162590143 : ℕ)^1043*3125000000000^787 ≤ 410677333947^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162590143 10000000000 410677333947 3125000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633090293/5000000000 : ℝ)^1043 ≤ (42746665473279/100000000000000 : ℝ)^787 := by
    have hnat : (2633090293 : ℕ)^1043*100000000000000^787 ≤ 42746665473279^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633090293 5000000000 42746665473279 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392576133/10000000000 : ℝ)^1043 ≤ (44111659823613/100000000000000 : ℝ)^787 := by
    have hnat : (5392576133 : ℕ)^1043*100000000000000^787 ≤ 44111659823613^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392576133 10000000000 44111659823613 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2162590143/10000000000 : ℝ), (2633090293/5000000000 : ℝ), (5392576133/10000000000 : ℝ)] ![(410677333947/3125000000000 : ℝ), (42746665473279/100000000000000 : ℝ), (44111659823613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2162590143/10000000000 : ℝ)|^1043 ≤ (410677333947/3125000000000 : ℝ)^787
        have hw : |(-2162590143/10000000000 : ℝ)|=(2162590143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633090293/5000000000 : ℝ)|^1043 ≤ (42746665473279/100000000000000 : ℝ)^787
        have hw : |(2633090293/5000000000 : ℝ)|=(2633090293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392576133/10000000000 : ℝ)|^1043 ≤ (44111659823613/100000000000000 : ℝ)^787
        have hw : |(5392576133/10000000000 : ℝ)|=(5392576133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s7_5 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (664065599/1250000000 : ℝ)*x 0 + (-2100303021/10000000000 : ℝ)*x 1 + (5392576161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664065599/1250000000 : ℝ)^1043 ≤ (43245930862251/100000000000000 : ℝ)^787 := by
    have hnat : (664065599 : ℕ)^1043*100000000000000^787 ≤ 43245930862251^787*1250000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664065599 1250000000 43245930862251 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2100303021/10000000000 : ℝ)^1043 ≤ (12642409002109/100000000000000 : ℝ)^787 := by
    have hnat : (2100303021 : ℕ)^1043*100000000000000^787 ≤ 12642409002109^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100303021 10000000000 12642409002109 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392576161/10000000000 : ℝ)^1043 ≤ (44111660127159/100000000000000 : ℝ)^787 := by
    have hnat : (5392576161 : ℕ)^1043*100000000000000^787 ≤ 44111660127159^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392576161 10000000000 44111660127159 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664065599/1250000000 : ℝ), (-2100303021/10000000000 : ℝ), (5392576161/10000000000 : ℝ)] ![(43245930862251/100000000000000 : ℝ), (12642409002109/100000000000000 : ℝ), (44111660127159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664065599/1250000000 : ℝ)|^1043 ≤ (43245930862251/100000000000000 : ℝ)^787
        have hw : |(664065599/1250000000 : ℝ)|=(664065599/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2100303021/10000000000 : ℝ)|^1043 ≤ (12642409002109/100000000000000 : ℝ)^787
        have hw : |(-2100303021/10000000000 : ℝ)|=(2100303021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392576161/10000000000 : ℝ)|^1043 ≤ (44111660127159/100000000000000 : ℝ)^787
        have hw : |(5392576161/10000000000 : ℝ)|=(5392576161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s7_6 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2656262409/5000000000 : ℝ)*x 0 + (2696288069/5000000000 : ℝ)*x 1 + (-262537877/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656262409/5000000000 : ℝ)^1043 ≤ (43245931142747/100000000000000 : ℝ)^787 := by
    have hnat : (2656262409 : ℕ)^1043*100000000000000^787 ≤ 43245931142747^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656262409 5000000000 43245931142747 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696288069/5000000000 : ℝ)^1043 ≤ (44111659877817/100000000000000 : ℝ)^787 := by
    have hnat : (2696288069 : ℕ)^1043*100000000000000^787 ≤ 44111659877817^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696288069 5000000000 44111659877817 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262537877/1250000000 : ℝ)^1043 ≤ (6321204481111/50000000000000 : ℝ)^787 := by
    have hnat : (262537877 : ℕ)^1043*50000000000000^787 ≤ 6321204481111^787*1250000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262537877 1250000000 6321204481111 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656262409/5000000000 : ℝ), (2696288069/5000000000 : ℝ), (-262537877/1250000000 : ℝ)] ![(43245931142747/100000000000000 : ℝ), (44111659877817/100000000000000 : ℝ), (6321204481111/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656262409/5000000000 : ℝ)|^1043 ≤ (43245931142747/100000000000000 : ℝ)^787
        have hw : |(2656262409/5000000000 : ℝ)|=(2656262409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696288069/5000000000 : ℝ)|^1043 ≤ (44111659877817/100000000000000 : ℝ)^787
        have hw : |(2696288069/5000000000 : ℝ)|=(2696288069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-262537877/1250000000 : ℝ)|^1043 ≤ (6321204481111/50000000000000 : ℝ)^787
        have hw : |(-262537877/1250000000 : ℝ)|=(262537877/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s7_7 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4363415229/10000000000 : ℝ)*x 0 + (898236501/2000000000 : ℝ)*x 1 + (211963889/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363415229/10000000000 : ℝ)^1043 ≤ (8329275098101/25000000000000 : ℝ)^787 := by
    have hnat : (4363415229 : ℕ)^1043*25000000000000^787 ≤ 8329275098101^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363415229 10000000000 8329275098101 25000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (898236501/2000000000 : ℝ)^1043 ≤ (34616132422719/100000000000000 : ℝ)^787 := by
    have hnat : (898236501 : ℕ)^1043*100000000000000^787 ≤ 34616132422719^787*2000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898236501 2000000000 34616132422719 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (211963889/500000000 : ℝ)^1043 ≤ (4008345895461/12500000000000 : ℝ)^787 := by
    have hnat : (211963889 : ℕ)^1043*12500000000000^787 ≤ 4008345895461^787*500000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211963889 500000000 4008345895461 12500000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363415229/10000000000 : ℝ), (898236501/2000000000 : ℝ), (211963889/500000000 : ℝ)] ![(8329275098101/25000000000000 : ℝ), (34616132422719/100000000000000 : ℝ), (4008345895461/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363415229/10000000000 : ℝ)|^1043 ≤ (8329275098101/25000000000000 : ℝ)^787
        have hw : |(4363415229/10000000000 : ℝ)|=(4363415229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(898236501/2000000000 : ℝ)|^1043 ≤ (34616132422719/100000000000000 : ℝ)^787
        have hw : |(898236501/2000000000 : ℝ)|=(898236501/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(211963889/500000000 : ℝ)|^1043 ≤ (4008345895461/12500000000000 : ℝ)^787
        have hw : |(211963889/500000000 : ℝ)|=(211963889/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1151_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7482467/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5679/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2841/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2811/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7031/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5679/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7031/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5679/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7031/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5679/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7031/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5679/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7031/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5679/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7031/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5679/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5679/50000 : ℝ) ^ (8343/2048 : ℝ) ≤ (56704093547573/400000000000000000 : ℝ) := by
    have hpowers : (5679/50000 : ℝ)^8343 ≤ (56704093547573/400000000000000000 : ℝ)^2048 := by
      have hnat : (5679 : ℕ)^8343*400000000000000000^2048 ≤ 56704093547573^2048*50000^8343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5679 50000 56704093547573 400000000000000000 8343 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5679/50000 : ℝ)) (X := (56704093547573/400000000000000000 : ℝ)) (by norm_num) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7031/50000 : ℝ) ^ (8343/2048 : ℝ) ≤ (33835569234360927/100000000000000000000 : ℝ) := by
    have hpowers : (7031/50000 : ℝ)^8343 ≤ (33835569234360927/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7031 : ℕ)^8343*100000000000000000000^2048 ≤ 33835569234360927^2048*50000^8343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7031 50000 33835569234360927 100000000000000000000 8343 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7031/50000 : ℝ)) (X := (33835569234360927/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (200056704093547573/200000000000000000 : ℝ) ≤ (5000347949071663/5000000000000000 : ℝ) ^ (8343/2048 : ℝ) := by
    have hpowers : (200056704093547573/200000000000000000 : ℝ)^2048 ≤ (5000347949071663/5000000000000000 : ℝ)^8343 := by
      have hnat : (200056704093547573 : ℕ)^2048*5000000000000000^8343 ≤ 5000347949071663^8343*200000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        200056704093547573 200000000000000000 5000347949071663 5000000000000000 2048 8343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000347949071663/5000000000000000 : ℝ)) (X := (200056704093547573/200000000000000000 : ℝ)) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048011592621254177/100000000000000000000 : ℝ) ≤ (5000589176175331/5000000000000000 : ℝ) ^ (8343/2048 : ℝ) := by
    have hpowers : (100048011592621254177/100000000000000000000 : ℝ)^2048 ≤ (5000589176175331/5000000000000000 : ℝ)^8343 := by
      have hnat : (100048011592621254177 : ℕ)^2048*5000000000000000^8343 ≤ 5000589176175331^8343*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048011592621254177 100000000000000000000 5000589176175331 5000000000000000 2048 8343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000589176175331/5000000000000000 : ℝ)) (X := (100048011592621254177/100000000000000000000 : ℝ)) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033835569234360927/50000000000000000000 : ℝ) ≤ (5000830403278999/5000000000000000 : ℝ) ^ (8343/2048 : ℝ) := by
    have hpowers : (50033835569234360927/50000000000000000000 : ℝ)^2048 ≤ (5000830403278999/5000000000000000 : ℝ)^8343 := by
      have hnat : (50033835569234360927 : ℕ)^2048*5000000000000000^8343 ≤ 5000830403278999^8343*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033835569234360927 50000000000000000000 5000830403278999 5000000000000000 2048 8343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000830403278999/5000000000000000 : ℝ)) (X := (50033835569234360927/50000000000000000000 : ℝ)) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(56704093547573/400000000000000000 : ℝ) ≤ ((211179080303169601/211250000000000000 : ℝ)+2*(60306775917/33800000000000 : ℝ)*(5679/50000 : ℝ))^(8343/2048 : ℝ) := by
    rw [show (211179080303169601/211250000000000000 : ℝ)+2*(60306775917/33800000000000 : ℝ)*(5679/50000 : ℝ)=(5000347949071663/5000000000000000 : ℝ) by norm_num, show 1+2*(56704093547573/400000000000000000 : ℝ)=(200056704093547573/200000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33835569234360927/100000000000000000000 : ℝ)+(56704093547573/400000000000000000 : ℝ) ≤ ((211179080303169601/211250000000000000 : ℝ)+(60306775917/33800000000000 : ℝ)*((7031/50000 : ℝ)+(5679/50000 : ℝ)))^(8343/2048 : ℝ) := by
    rw [show (211179080303169601/211250000000000000 : ℝ)+(60306775917/33800000000000 : ℝ)*((7031/50000 : ℝ)+(5679/50000 : ℝ))=(5000589176175331/5000000000000000 : ℝ) by norm_num, show 1+(33835569234360927/100000000000000000000 : ℝ)+(56704093547573/400000000000000000 : ℝ)=(100048011592621254177/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33835569234360927/100000000000000000000 : ℝ) ≤ ((211179080303169601/211250000000000000 : ℝ)+2*(60306775917/33800000000000 : ℝ)*(7031/50000 : ℝ))^(8343/2048 : ℝ) := by
    rw [show (211179080303169601/211250000000000000 : ℝ)+2*(60306775917/33800000000000 : ℝ)*(7031/50000 : ℝ)=(5000830403278999/5000000000000000 : ℝ) by norm_num, show 1+2*(33835569234360927/100000000000000000000 : ℝ)=(50033835569234360927/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (211179080303169601/211250000000000000 : ℝ)*(X 1 0+X 2 0)+(60306775917/33800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8343/2048 : ℝ)) (lo := (5679/50000 : ℝ)) (hi := (7031/50000 : ℝ)) (c := (211179080303169601/211250000000000000 : ℝ)) (alpha := (60306775917/33800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (211179080303169601/211250000000000000 : ℝ)*(X 0 1+X 2 1)+(60306775917/33800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8343/2048 : ℝ)) (lo := (5679/50000 : ℝ)) (hi := (7031/50000 : ℝ)) (c := (211179080303169601/211250000000000000 : ℝ)) (alpha := (60306775917/33800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (211179080303169601/211250000000000000 : ℝ)*(X 0 2+X 1 2)+(60306775917/33800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8343/2048 : ℝ)) (lo := (5679/50000 : ℝ)) (hi := (7031/50000 : ℝ)) (c := (211179080303169601/211250000000000000 : ℝ)) (alpha := (60306775917/33800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-135161581/625000000 : ℝ)*X 0 0+(215715867/400000000 : ℝ)*X 0 1+(82279081/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534473129/1000000000 : ℝ)*X 1 0+(-2227017971/10000000000 : ℝ)*X 1 1+(5265861189/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336182823/2500000000 : ℝ)*X 2 0+(526586119/1000000000 : ℝ)*X 2 1+(-2227017967/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4363405537/10000000000 : ℝ)*X 0 0+(2119319487/5000000000 : ℝ)*X 0 1+(4491819001/10000000000 : ℝ)*X 0 2+(4363405537/10000000000 : ℝ)*X 1 0+(2119319487/5000000000 : ℝ)*X 1 1+(4491819001/10000000000 : ℝ)*X 1 2+(4363405537/10000000000 : ℝ)*X 2 0+(2119319487/5000000000 : ℝ)*X 2 1+(4491819001/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2162590143/10000000000 : ℝ)*X 0 0+(2633090293/5000000000 : ℝ)*X 0 1+(5392576133/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664065599/1250000000 : ℝ)*X 1 0+(-2100303021/10000000000 : ℝ)*X 1 1+(5392576161/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656262409/5000000000 : ℝ)*X 2 0+(2696288069/5000000000 : ℝ)*X 2 1+(-262537877/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4363415229/10000000000 : ℝ)*X 0 0+(898236501/2000000000 : ℝ)*X 0 1+(211963889/500000000 : ℝ)*X 0 2+(4363415229/10000000000 : ℝ)*X 1 0+(898236501/2000000000 : ℝ)*X 1 1+(211963889/500000000 : ℝ)*X 1 2+(4363415229/10000000000 : ℝ)*X 2 0+(898236501/2000000000 : ℝ)*X 2 1+(211963889/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43060628311075457042335539/5281250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10068501/625000000000 : ℝ)*(base19) + (150746793/10000000000000 : ℝ)*(base23) + (28444099/50000000000000 : ℝ)*(lower2) + (202648227/100000000000000 : ℝ)*(upper3) + (130915991/100000000000000 : ℝ)*(upper5) + (2955427654803321/50000000000000 : ℝ)*(major0) + (2955427654803321/50000000000000 : ℝ)*(major1) + (2955427654803321/50000000000000 : ℝ)*(major2) + (7871862048529029/100000000000000 : ℝ)*(sp0) + (7871904942075339/100000000000000 : ℝ)*(sp1) + (787190504556757/10000000000000 : ℝ)*(sp2) + (3949780135710837/100000000000000 : ℝ)*(sp3) + (44504506471/100000000000000 : ℝ)*(sp4) + (11829341937/50000000000000 : ℝ)*(sp7) + (394980379439471/10000000000000 : ℝ)*(f.failure) + (15743813106071/200000000000 : ℝ)*(f.sum) + (1675008787447/845000000000000000000000000 : ℝ)*base65 + (265439498558036329/10562500000000000000000000000000 : ℝ)*base68 + (70551490723223829/10562500000000000000000000000000 : ℝ)*base70 + (49449499957036329/10562500000000000000000000000000 : ℝ)*base72 + (620847205299/422500000000000000000000000 : ℝ)*base74 + (135903274132473829/10562500000000000000000000000000 : ℝ)*base76 + (743099267661329/10562500000000000000000000000000 : ℝ)*base78 + (76993489464973829/10562500000000000000000000000000 : ℝ)*base80 + (671688712379/422500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (745043/50000000000000000000 : ℝ)*base90 + (745043/50000000000000000000 : ℝ)*base92 + (745043/50000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (58130438176219912669677723/10562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (180036563/20000000000000 : ℝ)*(base19) + (1058865807/100000000000000 : ℝ)*(base23) + (14255139/12500000000000 : ℝ)*(upper3) + (50474849/100000000000000 : ℝ)*(lower4) + (93280957/100000000000000 : ℝ)*(upper5) + (5940712259973547/100000000000000 : ℝ)*(major0) + (5940712259973547/100000000000000 : ℝ)*(major1) + (5940712259973547/100000000000000 : ℝ)*(major2) + (25479541287/100000000000000 : ℝ)*(sp1) + (29595361953/100000000000000 : ℝ)*(sp2) + (3955834633883129/50000000000000 : ℝ)*(sp4) + (7911642888042157/100000000000000 : ℝ)*(sp5) + (7911638613538499/100000000000000 : ℝ)*(sp6) + (992438767182927/25000000000000 : ℝ)*(sp7) + (992438767182927/25000000000000 : ℝ)*(f.failure) + (3955834633883129/50000000000000 : ℝ)*(f.sum) + (3840584074621/1690000000000000000000000000 : ℝ)*base66 + (88298852066961503/21125000000000000000000000000000 : ℝ)*base68 + (132676833016211503/21125000000000000000000000000000 : ℝ)*base70 + (426348960102211503/21125000000000000000000000000000 : ℝ)*base72 + (6000527041059/1690000000000000000000000000 : ℝ)*base73 + (669761139992961503/21125000000000000000000000000000 : ℝ)*base76 + (302173567026711503/21125000000000000000000000000000 : ℝ)*base78 + (559208347408961503/21125000000000000000000000000000 : ℝ)*base80 + (2579321226149/1690000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (490909/125000000000000000000 : ℝ)*base89 + (490909/125000000000000000000 : ℝ)*base91 + (490909/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1151_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7482467/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5679/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2841/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2811/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1151_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1151_s8_0 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-540648303/2500000000 : ℝ)*x 0 + (674103813/1250000000 : ℝ)*x 1 + (5265921943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540648303/2500000000 : ℝ)^1043 ≤ (13141699402581/100000000000000 : ℝ)^787 := by
    have hnat : (540648303 : ℕ)^1043*100000000000000^787 ≤ 13141699402581^787*2500000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540648303 2500000000 13141699402581 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674103813/1250000000 : ℝ)^1043 ≤ (5514302182991/12500000000000 : ℝ)^787 := by
    have hnat : (674103813 : ℕ)^1043*12500000000000^787 ≤ 5514302182991^787*1250000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674103813 1250000000 5514302182991 12500000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265921943/10000000000 : ℝ)^1043 ≤ (21371941556609/50000000000000 : ℝ)^787 := by
    have hnat : (5265921943 : ℕ)^1043*50000000000000^787 ≤ 21371941556609^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265921943 10000000000 21371941556609 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-540648303/2500000000 : ℝ), (674103813/1250000000 : ℝ), (5265921943/10000000000 : ℝ)] ![(13141699402581/100000000000000 : ℝ), (5514302182991/12500000000000 : ℝ), (21371941556609/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-540648303/2500000000 : ℝ)|^1043 ≤ (13141699402581/100000000000000 : ℝ)^787
        have hw : |(-540648303/2500000000 : ℝ)|=(540648303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674103813/1250000000 : ℝ)|^1043 ≤ (5514302182991/12500000000000 : ℝ)^787
        have hw : |(674103813/1250000000 : ℝ)|=(674103813/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265921943/10000000000 : ℝ)|^1043 ≤ (21371941556609/50000000000000 : ℝ)^787
        have hw : |(5265921943/10000000000 : ℝ)|=(5265921943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s8_1 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5344713933/10000000000 : ℝ)*x 0 + (-2226960489/10000000000 : ℝ)*x 1 + (1316480519/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344713933/10000000000 : ℝ)^1043 ≤ (1362298106273/3125000000000 : ℝ)^787 := by
    have hnat : (5344713933 : ℕ)^1043*3125000000000^787 ≤ 1362298106273^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344713933 10000000000 1362298106273 3125000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2226960489/10000000000 : ℝ)^1043 ≤ (273251520683/2000000000000 : ℝ)^787 := by
    have hnat : (2226960489 : ℕ)^1043*2000000000000^787 ≤ 273251520683^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2226960489 10000000000 273251520683 2000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316480519/2500000000 : ℝ)^1043 ≤ (21371942271979/50000000000000 : ℝ)^787 := by
    have hnat : (1316480519 : ℕ)^1043*50000000000000^787 ≤ 21371942271979^787*2500000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316480519 2500000000 21371942271979 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344713933/10000000000 : ℝ), (-2226960489/10000000000 : ℝ), (1316480519/2500000000 : ℝ)] ![(1362298106273/3125000000000 : ℝ), (273251520683/2000000000000 : ℝ), (21371942271979/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344713933/10000000000 : ℝ)|^1043 ≤ (1362298106273/3125000000000 : ℝ)^787
        have hw : |(5344713933/10000000000 : ℝ)|=(5344713933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2226960489/10000000000 : ℝ)|^1043 ≤ (273251520683/2000000000000 : ℝ)^787
        have hw : |(-2226960489/10000000000 : ℝ)|=(2226960489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316480519/2500000000 : ℝ)|^1043 ≤ (21371942271979/50000000000000 : ℝ)^787
        have hw : |(1316480519/2500000000 : ℝ)|=(1316480519/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s8_2 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (267235701/500000000 : ℝ)*x 0 + (5265921991/10000000000 : ℝ)*x 1 + (-1113480243/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267235701/500000000 : ℝ)^1043 ≤ (21796770170583/50000000000000 : ℝ)^787 := by
    have hnat : (267235701 : ℕ)^1043*50000000000000^787 ≤ 21796770170583^787*500000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267235701 500000000 21796770170583 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265921991/10000000000 : ℝ)^1043 ≤ (1709755345183/4000000000000 : ℝ)^787 := by
    have hnat : (5265921991 : ℕ)^1043*4000000000000^787 ≤ 1709755345183^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265921991 10000000000 1709755345183 4000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1113480243/5000000000 : ℝ)^1043 ≤ (6831288004879/50000000000000 : ℝ)^787 := by
    have hnat : (1113480243 : ℕ)^1043*50000000000000^787 ≤ 6831288004879^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1113480243 5000000000 6831288004879 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267235701/500000000 : ℝ), (5265921991/10000000000 : ℝ), (-1113480243/5000000000 : ℝ)] ![(21796770170583/50000000000000 : ℝ), (1709755345183/4000000000000 : ℝ), (6831288004879/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267235701/500000000 : ℝ)|^1043 ≤ (21796770170583/50000000000000 : ℝ)^787
        have hw : |(267235701/500000000 : ℝ)|=(267235701/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265921991/10000000000 : ℝ)|^1043 ≤ (1709755345183/4000000000000 : ℝ)^787
        have hw : |(5265921991/10000000000 : ℝ)|=(5265921991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1113480243/5000000000 : ℝ)|^1043 ≤ (6831288004879/50000000000000 : ℝ)^787
        have hw : |(-1113480243/5000000000 : ℝ)|=(1113480243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s8_3 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1090852219/2500000000 : ℝ)*x 0 + (4238765087/10000000000 : ℝ)*x 1 + (140365373/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090852219/2500000000 : ℝ)^1043 ≤ (16658518052271/50000000000000 : ℝ)^787 := by
    have hnat : (1090852219 : ℕ)^1043*50000000000000^787 ≤ 16658518052271^787*2500000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090852219 2500000000 16658518052271 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4238765087/10000000000 : ℝ)^1043 ≤ (32061627653577/100000000000000 : ℝ)^787 := by
    have hnat : (4238765087 : ℕ)^1043*100000000000000^787 ≤ 32061627653577^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238765087 10000000000 32061627653577 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (140365373/312500000 : ℝ)^1043 ≤ (34621336225119/100000000000000 : ℝ)^787 := by
    have hnat : (140365373 : ℕ)^1043*100000000000000^787 ≤ 34621336225119^787*312500000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140365373 312500000 34621336225119 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1090852219/2500000000 : ℝ), (4238765087/10000000000 : ℝ), (140365373/312500000 : ℝ)] ![(16658518052271/50000000000000 : ℝ), (32061627653577/100000000000000 : ℝ), (34621336225119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1090852219/2500000000 : ℝ)|^1043 ≤ (16658518052271/50000000000000 : ℝ)^787
        have hw : |(1090852219/2500000000 : ℝ)|=(1090852219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4238765087/10000000000 : ℝ)|^1043 ≤ (32061627653577/100000000000000 : ℝ)^787
        have hw : |(4238765087/10000000000 : ℝ)|=(4238765087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(140365373/312500000 : ℝ)|^1043 ≤ (34621336225119/100000000000000 : ℝ)^787
        have hw : |(140365373/312500000 : ℝ)|=(140365373/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s8_4 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1081299017/5000000000 : ℝ)*x 0 + (526624077/1000000000 : ℝ)*x 1 + (107850211/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081299017/5000000000 : ℝ)^1043 ≤ (3285434559179/25000000000000 : ℝ)^787 := by
    have hnat : (1081299017 : ℕ)^1043*25000000000000^787 ≤ 3285434559179^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081299017 5000000000 3285434559179 25000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526624077/1000000000 : ℝ)^1043 ≤ (42747312910893/100000000000000 : ℝ)^787 := by
    have hnat : (526624077 : ℕ)^1043*100000000000000^787 ≤ 42747312910893^787*1000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526624077 1000000000 42747312910893 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (107850211/200000000 : ℝ)^1043 ≤ (44110948844061/100000000000000 : ℝ)^787 := by
    have hnat : (107850211 : ℕ)^1043*100000000000000^787 ≤ 44110948844061^787*200000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107850211 200000000 44110948844061 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1081299017/5000000000 : ℝ), (526624077/1000000000 : ℝ), (107850211/200000000 : ℝ)] ![(3285434559179/25000000000000 : ℝ), (42747312910893/100000000000000 : ℝ), (44110948844061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1081299017/5000000000 : ℝ)|^1043 ≤ (3285434559179/25000000000000 : ℝ)^787
        have hw : |(-1081299017/5000000000 : ℝ)|=(1081299017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526624077/1000000000 : ℝ)|^1043 ≤ (42747312910893/100000000000000 : ℝ)^787
        have hw : |(526624077/1000000000 : ℝ)|=(526624077/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(107850211/200000000 : ℝ)|^1043 ≤ (44110948844061/100000000000000 : ℝ)^787
        have hw : |(107850211/200000000 : ℝ)|=(107850211/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s8_5 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (664067467/1250000000 : ℝ)*x 0 + (-2100371973/10000000000 : ℝ)*x 1 + (107850211/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664067467/1250000000 : ℝ)^1043 ≤ (2702880755187/6250000000000 : ℝ)^787 := by
    have hnat : (664067467 : ℕ)^1043*6250000000000^787 ≤ 2702880755187^787*1250000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664067467 1250000000 2702880755187 6250000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2100371973/10000000000 : ℝ)^1043 ≤ (6321479528887/50000000000000 : ℝ)^787 := by
    have hnat : (2100371973 : ℕ)^1043*50000000000000^787 ≤ 6321479528887^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100371973 10000000000 6321479528887 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (107850211/200000000 : ℝ)^1043 ≤ (44110948844061/100000000000000 : ℝ)^787 := by
    have hnat : (107850211 : ℕ)^1043*100000000000000^787 ≤ 44110948844061^787*200000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107850211 200000000 44110948844061 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664067467/1250000000 : ℝ), (-2100371973/10000000000 : ℝ), (107850211/200000000 : ℝ)] ![(2702880755187/6250000000000 : ℝ), (6321479528887/50000000000000 : ℝ), (44110948844061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664067467/1250000000 : ℝ)|^1043 ≤ (2702880755187/6250000000000 : ℝ)^787
        have hw : |(664067467/1250000000 : ℝ)|=(664067467/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2100371973/10000000000 : ℝ)|^1043 ≤ (6321479528887/50000000000000 : ℝ)^787
        have hw : |(-2100371973/10000000000 : ℝ)|=(2100371973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(107850211/200000000 : ℝ)|^1043 ≤ (44110948844061/100000000000000 : ℝ)^787
        have hw : |(107850211/200000000 : ℝ)|=(107850211/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s8_6 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (664067467/1250000000 : ℝ)*x 0 + (107850211/200000000 : ℝ)*x 1 + (-2100371973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664067467/1250000000 : ℝ)^1043 ≤ (2702880755187/6250000000000 : ℝ)^787 := by
    have hnat : (664067467 : ℕ)^1043*6250000000000^787 ≤ 2702880755187^787*1250000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664067467 1250000000 2702880755187 6250000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107850211/200000000 : ℝ)^1043 ≤ (44110948844061/100000000000000 : ℝ)^787 := by
    have hnat : (107850211 : ℕ)^1043*100000000000000^787 ≤ 44110948844061^787*200000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107850211 200000000 44110948844061 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2100371973/10000000000 : ℝ)^1043 ≤ (6321479528887/50000000000000 : ℝ)^787 := by
    have hnat : (2100371973 : ℕ)^1043*50000000000000^787 ≤ 6321479528887^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100371973 10000000000 6321479528887 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664067467/1250000000 : ℝ), (107850211/200000000 : ℝ), (-2100371973/10000000000 : ℝ)] ![(2702880755187/6250000000000 : ℝ), (44110948844061/100000000000000 : ℝ), (6321479528887/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664067467/1250000000 : ℝ)|^1043 ≤ (2702880755187/6250000000000 : ℝ)^787
        have hw : |(664067467/1250000000 : ℝ)|=(664067467/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(107850211/200000000 : ℝ)|^1043 ≤ (44110948844061/100000000000000 : ℝ)^787
        have hw : |(107850211/200000000 : ℝ)|=(107850211/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2100371973/10000000000 : ℝ)|^1043 ≤ (6321479528887/50000000000000 : ℝ)^787
        have hw : |(-2100371973/10000000000 : ℝ)|=(2100371973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s8_7 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (68178413/156250000 : ℝ)*x 0 + (56138209/125000000 : ℝ)*x 1 + (847880543/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (68178413/156250000 : ℝ)^1043 ≤ (8329283201127/25000000000000 : ℝ)^787 := by
    have hnat : (68178413 : ℕ)^1043*25000000000000^787 ≤ 8329283201127^787*156250000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68178413 156250000 8329283201127 25000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56138209/125000000 : ℝ)^1043 ≤ (34614847567207/100000000000000 : ℝ)^787 := by
    have hnat : (56138209 : ℕ)^1043*100000000000000^787 ≤ 34614847567207^787*125000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56138209 125000000 34614847567207 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (847880543/2000000000 : ℝ)^1043 ≤ (32068019609897/100000000000000 : ℝ)^787 := by
    have hnat : (847880543 : ℕ)^1043*100000000000000^787 ≤ 32068019609897^787*2000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847880543 2000000000 32068019609897 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(68178413/156250000 : ℝ), (56138209/125000000 : ℝ), (847880543/2000000000 : ℝ)] ![(8329283201127/25000000000000 : ℝ), (34614847567207/100000000000000 : ℝ), (32068019609897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(68178413/156250000 : ℝ)|^1043 ≤ (8329283201127/25000000000000 : ℝ)^787
        have hw : |(68178413/156250000 : ℝ)|=(68178413/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(56138209/125000000 : ℝ)|^1043 ≤ (34614847567207/100000000000000 : ℝ)^787
        have hw : |(56138209/125000000 : ℝ)|=(56138209/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(847880543/2000000000 : ℝ)|^1043 ≤ (32068019609897/100000000000000 : ℝ)^787
        have hw : |(847880543/2000000000 : ℝ)|=(847880543/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1151_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7482467/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2811/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2841/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2273/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7027/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2811/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2841/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2811/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2841/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2811/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2841/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2811/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2841/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2811/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2841/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2811/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2841/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2841/25000 : ℝ) ^ (8343/2048 : ℝ) ≤ (14206554924294157/100000000000000000000 : ℝ) := by
    have hpowers : (2841/25000 : ℝ)^8343 ≤ (14206554924294157/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2841 : ℕ)^8343*100000000000000000000^2048 ≤ 14206554924294157^2048*25000^8343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2841 25000 14206554924294157 100000000000000000000 8343 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2841/25000 : ℝ)) (X := (14206554924294157/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2811/20000 : ℝ) ^ (8343/2048 : ℝ) ≤ (33767007079680691/100000000000000000000 : ℝ) := by
    have hpowers : (2811/20000 : ℝ)^8343 ≤ (33767007079680691/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2811 : ℕ)^8343*100000000000000000000^2048 ≤ 33767007079680691^2048*20000^8343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2811 20000 33767007079680691 100000000000000000000 8343 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2811/20000 : ℝ)) (X := (33767007079680691/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014206554924294157/50000000000000000000 : ℝ) ≤ (2500174349192437/2500000000000000 : ℝ) ^ (8343/2048 : ℝ) := by
    have hpowers : (50014206554924294157/50000000000000000000 : ℝ)^2048 ≤ (2500174349192437/2500000000000000 : ℝ)^8343 := by
      have hnat : (50014206554924294157 : ℕ)^2048*2500000000000000^8343 ≤ 2500174349192437^8343*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014206554924294157 50000000000000000000 2500174349192437 2500000000000000 2048 8343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500174349192437/2500000000000000 : ℝ)) (X := (50014206554924294157/50000000000000000000 : ℝ)) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (1563249586906312107/1562500000000000000 : ℝ) ≤ (2500294354782763/2500000000000000 : ℝ) ^ (8343/2048 : ℝ) := by
    have hpowers : (1563249586906312107/1562500000000000000 : ℝ)^2048 ≤ (2500294354782763/2500000000000000 : ℝ)^8343 := by
      have hnat : (1563249586906312107 : ℕ)^2048*2500000000000000^8343 ≤ 2500294354782763^8343*1562500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563249586906312107 1562500000000000000 2500294354782763 2500000000000000 2048 8343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500294354782763/2500000000000000 : ℝ)) (X := (1563249586906312107/1562500000000000000 : ℝ)) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033767007079680691/50000000000000000000 : ℝ) ≤ (2500414360373089/2500000000000000 : ℝ) ^ (8343/2048 : ℝ) := by
    have hpowers : (50033767007079680691/50000000000000000000 : ℝ)^2048 ≤ (2500414360373089/2500000000000000 : ℝ)^8343 := by
      have hnat : (50033767007079680691 : ℕ)^2048*2500000000000000^8343 ≤ 2500414360373089^8343*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033767007079680691 50000000000000000000 2500414360373089 2500000000000000 2048 8343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500414360373089/2500000000000000 : ℝ)) (X := (50033767007079680691/50000000000000000000 : ℝ)) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14206554924294157/100000000000000000000 : ℝ) ≤ ((32489090273526177/32500000000000000 : ℝ)+2*(869605727/487500000000 : ℝ)*(2841/25000 : ℝ))^(8343/2048 : ℝ) := by
    rw [show (32489090273526177/32500000000000000 : ℝ)+2*(869605727/487500000000 : ℝ)*(2841/25000 : ℝ)=(2500174349192437/2500000000000000 : ℝ) by norm_num, show 1+2*(14206554924294157/100000000000000000000 : ℝ)=(50014206554924294157/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33767007079680691/100000000000000000000 : ℝ)+(14206554924294157/100000000000000000000 : ℝ) ≤ ((32489090273526177/32500000000000000 : ℝ)+(869605727/487500000000 : ℝ)*((2811/20000 : ℝ)+(2841/25000 : ℝ)))^(8343/2048 : ℝ) := by
    rw [show (32489090273526177/32500000000000000 : ℝ)+(869605727/487500000000 : ℝ)*((2811/20000 : ℝ)+(2841/25000 : ℝ))=(2500294354782763/2500000000000000 : ℝ) by norm_num, show 1+(33767007079680691/100000000000000000000 : ℝ)+(14206554924294157/100000000000000000000 : ℝ)=(1563249586906312107/1562500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33767007079680691/100000000000000000000 : ℝ) ≤ ((32489090273526177/32500000000000000 : ℝ)+2*(869605727/487500000000 : ℝ)*(2811/20000 : ℝ))^(8343/2048 : ℝ) := by
    rw [show (32489090273526177/32500000000000000 : ℝ)+2*(869605727/487500000000 : ℝ)*(2811/20000 : ℝ)=(2500414360373089/2500000000000000 : ℝ) by norm_num, show 1+2*(33767007079680691/100000000000000000000 : ℝ)=(50033767007079680691/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (32489090273526177/32500000000000000 : ℝ)*(X 1 0+X 2 0)+(869605727/487500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8343/2048 : ℝ)) (lo := (2841/25000 : ℝ)) (hi := (2811/20000 : ℝ)) (c := (32489090273526177/32500000000000000 : ℝ)) (alpha := (869605727/487500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (32489090273526177/32500000000000000 : ℝ)*(X 0 1+X 2 1)+(869605727/487500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8343/2048 : ℝ)) (lo := (2841/25000 : ℝ)) (hi := (2811/20000 : ℝ)) (c := (32489090273526177/32500000000000000 : ℝ)) (alpha := (869605727/487500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (32489090273526177/32500000000000000 : ℝ)*(X 0 2+X 1 2)+(869605727/487500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8343/2048 : ℝ)) (lo := (2841/25000 : ℝ)) (hi := (2811/20000 : ℝ)) (c := (32489090273526177/32500000000000000 : ℝ)) (alpha := (869605727/487500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-540648303/2500000000 : ℝ)*X 0 0+(674103813/1250000000 : ℝ)*X 0 1+(5265921943/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344713933/10000000000 : ℝ)*X 1 0+(-2226960489/10000000000 : ℝ)*X 1 1+(1316480519/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267235701/500000000 : ℝ)*X 2 0+(5265921991/10000000000 : ℝ)*X 2 1+(-1113480243/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1090852219/2500000000 : ℝ)*X 0 0+(4238765087/10000000000 : ℝ)*X 0 1+(140365373/312500000 : ℝ)*X 0 2+(1090852219/2500000000 : ℝ)*X 1 0+(4238765087/10000000000 : ℝ)*X 1 1+(140365373/312500000 : ℝ)*X 1 2+(1090852219/2500000000 : ℝ)*X 2 0+(4238765087/10000000000 : ℝ)*X 2 1+(140365373/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1081299017/5000000000 : ℝ)*X 0 0+(526624077/1000000000 : ℝ)*X 0 1+(107850211/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664067467/1250000000 : ℝ)*X 1 0+(-2100371973/10000000000 : ℝ)*X 1 1+(107850211/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664067467/1250000000 : ℝ)*X 2 0+(107850211/200000000 : ℝ)*X 2 1+(-2100371973/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((68178413/156250000 : ℝ)*X 0 0+(56138209/125000000 : ℝ)*X 0 1+(847880543/2000000000 : ℝ)*X 0 2+(68178413/156250000 : ℝ)*X 1 0+(56138209/125000000 : ℝ)*X 1 1+(847880543/2000000000 : ℝ)*X 1 2+(68178413/156250000 : ℝ)*X 2 0+(56138209/125000000 : ℝ)*X 2 1+(847880543/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1718121885108595524426123/162500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2208338941/100000000000000 : ℝ)*(base19) + (1077006599/50000000000000 : ℝ)*(base23) + (97590003/100000000000000 : ℝ)*(lower2) + (303816189/100000000000000 : ℝ)*(upper3) + (197538027/100000000000000 : ℝ)*(upper5) + (1183360012800867/20000000000000 : ℝ)*(major0) + (1183360012800867/20000000000000 : ℝ)*(major1) + (1183360012800867/20000000000000 : ℝ)*(major2) + (63038053283073/800000000000 : ℝ)*(sp0) + (1969955329174537/25000000000000 : ℝ)*(sp1) + (7879821371023891/100000000000000 : ℝ)*(sp2) + (1976871146682021/50000000000000 : ℝ)*(sp3) + (16716163241/25000000000000 : ℝ)*(sp4) + (33957172269/100000000000000 : ℝ)*(sp7) + (395377625053631/10000000000000 : ℝ)*(f.failure) + (7879823525037089/100000000000000 : ℝ)*(f.sum) + (523593353/3250000000000000000000000 : ℝ)*base65 + (780570333407343/50000000000000000000000000000 : ℝ)*base67 + (650789828007343/50000000000000000000000000000 : ℝ)*base69 + (361464890092657/50000000000000000000000000000 : ℝ)*base72 + (2370241841/6500000000000000000000000 : ℝ)*base74 + (1056970319357343/50000000000000000000000000000 : ℝ)*base75 + (397947323107343/50000000000000000000000000000 : ℝ)*base77 + (819180548357343/50000000000000000000000000000 : ℝ)*base79 + (26849319249/13000000000000000000000000 : ℝ)*base82 + (312323/50000000000000000000 : ℝ)*base90 + (312323/50000000000000000000 : ℝ)*base92 + (312323/50000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1466770152736805743516161/162500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (823748109/50000000000000 : ℝ)*(base19) + (895207131/50000000000000 : ℝ)*(base23) + (115583283/20000000000000 : ℝ)*(lower1) + (90582869/50000000000000 : ℝ)*(upper3) + (65017019/100000000000000 : ℝ)*(lower4) + (184235769/100000000000000 : ℝ)*(upper5) + (594659525683923/10000000000000 : ℝ)*(major0) + (594659525683923/10000000000000 : ℝ)*(major1) + (594659525683923/10000000000000 : ℝ)*(major2) + (1695263367/50000000000000 : ℝ)*(sp2) + (1979875989022787/25000000000000 : ℝ)*(sp4) + (791950230859493/10000000000000 : ℝ)*(sp5) + (7919498775150151/100000000000000 : ℝ)*(sp6) + (1986843128355671/50000000000000 : ℝ)*(sp7) + (1986843128355671/50000000000000 : ℝ)*(f.failure) + (1979875989022787/25000000000000 : ℝ)*(f.sum) + (10956142643/1625000000000000000000000 : ℝ)*base66 + (166158565765567/25000000000000000000000000000 : ℝ)*base67 + (331263997515567/25000000000000000000000000000 : ℝ)*base69 + (4639124265165567/25000000000000000000000000000 : ℝ)*base71 + (12694566719/6500000000000000000000000 : ℝ)*base74 + (2497516495015567/25000000000000000000000000000 : ℝ)*base75 + (464239956765567/25000000000000000000000000000 : ℝ)*base77 + (333361153665567/25000000000000000000000000000 : ℝ)*base79 + (88140886633/13000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (2479643/250000000000000000000 : ℝ)*base90 + (2479643/250000000000000000000 : ℝ)*base92 + (2479643/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1151_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7482467/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2811/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2841/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2273/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7027/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1151_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1151_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7482467/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (354/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2273/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7027/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1151_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1151_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1151_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7482467/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (354/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2273/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7027/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1151_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

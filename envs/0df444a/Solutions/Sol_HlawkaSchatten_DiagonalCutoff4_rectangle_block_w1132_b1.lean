-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1132_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:26:59.056061+00:00
-- url     : https://prove2.me/submissions/241ce881-9538-4473-99ac-06170d07bc39

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
theorem support_rectangle_w1132_s3_0 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-541941239/2500000000 : ℝ)*x 0 + (2715106063/5000000000 : ℝ)*x 1 + (32694621/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541941239/2500000000 : ℝ)^8325 ≤ (2632707101791/20000000000000 : ℝ)^6277 := by
    have hnat : (541941239 : ℕ)^8325*20000000000000^6277 ≤ 2632707101791^6277*2500000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541941239 2500000000 2632707101791 20000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2715106063/5000000000 : ℝ)^8325 ≤ (44493373505401/100000000000000 : ℝ)^6277 := by
    have hnat : (2715106063 : ℕ)^8325*100000000000000^6277 ≤ 44493373505401^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715106063 5000000000 44493373505401 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32694621/62500000 : ℝ)^8325 ≤ (42343090975411/100000000000000 : ℝ)^6277 := by
    have hnat : (32694621 : ℕ)^8325*100000000000000^6277 ≤ 42343090975411^6277*62500000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32694621 62500000 42343090975411 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-541941239/2500000000 : ℝ), (2715106063/5000000000 : ℝ), (32694621/62500000 : ℝ)] ![(2632707101791/20000000000000 : ℝ), (44493373505401/100000000000000 : ℝ), (42343090975411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-541941239/2500000000 : ℝ)|^8325 ≤ (2632707101791/20000000000000 : ℝ)^6277
        have hw : |(-541941239/2500000000 : ℝ)|=(541941239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2715106063/5000000000 : ℝ)|^8325 ≤ (44493373505401/100000000000000 : ℝ)^6277
        have hw : |(2715106063/5000000000 : ℝ)|=(2715106063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(32694621/62500000 : ℝ)|^8325 ≤ (42343090975411/100000000000000 : ℝ)^6277
        have hw : |(32694621/62500000 : ℝ)|=(32694621/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s3_1 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (107080687/200000000 : ℝ)*x 0 + (-2269546557/10000000000 : ℝ)*x 1 + (1307784809/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107080687/200000000 : ℝ)^8325 ≤ (43667448252827/100000000000000 : ℝ)^6277 := by
    have hnat : (107080687 : ℕ)^8325*100000000000000^6277 ≤ 43667448252827^6277*200000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107080687 200000000 43667448252827 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2269546557/10000000000 : ℝ)^8325 ≤ (13989462090839/100000000000000 : ℝ)^6277 := by
    have hnat : (2269546557 : ℕ)^8325*100000000000000^6277 ≤ 13989462090839^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2269546557 10000000000 13989462090839 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1307784809/2500000000 : ℝ)^8325 ≤ (42343089644221/100000000000000 : ℝ)^6277 := by
    have hnat : (1307784809 : ℕ)^8325*100000000000000^6277 ≤ 42343089644221^6277*2500000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307784809 2500000000 42343089644221 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107080687/200000000 : ℝ), (-2269546557/10000000000 : ℝ), (1307784809/2500000000 : ℝ)] ![(43667448252827/100000000000000 : ℝ), (13989462090839/100000000000000 : ℝ), (42343089644221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107080687/200000000 : ℝ)|^8325 ≤ (43667448252827/100000000000000 : ℝ)^6277
        have hw : |(107080687/200000000 : ℝ)|=(107080687/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2269546557/10000000000 : ℝ)|^8325 ≤ (13989462090839/100000000000000 : ℝ)^6277
        have hw : |(-2269546557/10000000000 : ℝ)|=(2269546557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1307784809/2500000000 : ℝ)|^8325 ≤ (42343089644221/100000000000000 : ℝ)^6277
        have hw : |(1307784809/2500000000 : ℝ)|=(1307784809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s3_2 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (133850861/250000000 : ℝ)*x 0 + (5231139331/10000000000 : ℝ)*x 1 + (-283693289/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133850861/250000000 : ℝ)^8325 ≤ (43667449226361/100000000000000 : ℝ)^6277 := by
    have hnat : (133850861 : ℕ)^8325*100000000000000^6277 ≤ 43667449226361^6277*250000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133850861 250000000 43667449226361 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5231139331/10000000000 : ℝ)^8325 ≤ (10585772666021/25000000000000 : ℝ)^6277 := by
    have hnat : (5231139331 : ℕ)^8325*25000000000000^6277 ≤ 10585772666021^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231139331 10000000000 10585772666021 25000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (283693289/1250000000 : ℝ)^8325 ≤ (2797892017587/20000000000000 : ℝ)^6277 := by
    have hnat : (283693289 : ℕ)^8325*20000000000000^6277 ≤ 2797892017587^6277*1250000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283693289 1250000000 2797892017587 20000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133850861/250000000 : ℝ), (5231139331/10000000000 : ℝ), (-283693289/1250000000 : ℝ)] ![(43667449226361/100000000000000 : ℝ), (10585772666021/25000000000000 : ℝ), (2797892017587/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133850861/250000000 : ℝ)|^8325 ≤ (43667449226361/100000000000000 : ℝ)^6277
        have hw : |(133850861/250000000 : ℝ)|=(133850861/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5231139331/10000000000 : ℝ)|^8325 ≤ (10585772666021/25000000000000 : ℝ)^6277
        have hw : |(5231139331/10000000000 : ℝ)|=(5231139331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-283693289/1250000000 : ℝ)|^8325 ≤ (2797892017587/20000000000000 : ℝ)^6277
        have hw : |(-283693289/1250000000 : ℝ)|=(283693289/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s3_3 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (872752341/2000000000 : ℝ)*x 0 + (2085291441/5000000000 : ℝ)*x 1 + (4565855931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872752341/2000000000 : ℝ)^8325 ≤ (33293411588941/100000000000000 : ℝ)^6277 := by
    have hnat : (872752341 : ℕ)^8325*100000000000000^6277 ≤ 33293411588941^6277*2000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872752341 2000000000 33293411588941 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085291441/5000000000 : ℝ)^8325 ≤ (31352931803701/100000000000000 : ℝ)^6277 := by
    have hnat : (2085291441 : ℕ)^8325*100000000000000^6277 ≤ 31352931803701^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085291441 5000000000 31352931803701 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4565855931/10000000000 : ℝ)^8325 ≤ (35353656598403/100000000000000 : ℝ)^6277 := by
    have hnat : (4565855931 : ℕ)^8325*100000000000000^6277 ≤ 35353656598403^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4565855931 10000000000 35353656598403 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872752341/2000000000 : ℝ), (2085291441/5000000000 : ℝ), (4565855931/10000000000 : ℝ)] ![(33293411588941/100000000000000 : ℝ), (31352931803701/100000000000000 : ℝ), (35353656598403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872752341/2000000000 : ℝ)|^8325 ≤ (33293411588941/100000000000000 : ℝ)^6277
        have hw : |(872752341/2000000000 : ℝ)|=(872752341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2085291441/5000000000 : ℝ)|^8325 ≤ (31352931803701/100000000000000 : ℝ)^6277
        have hw : |(2085291441/5000000000 : ℝ)|=(2085291441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4565855931/10000000000 : ℝ)|^8325 ≤ (35353656598403/100000000000000 : ℝ)^6277
        have hw : |(4565855931/10000000000 : ℝ)|=(4565855931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s3_4 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2167783527/10000000000 : ℝ)*x 0 + (5231917371/10000000000 : ℝ)*x 1 + (2714714869/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2167783527/10000000000 : ℝ)^8325 ≤ (6581842536701/50000000000000 : ℝ)^6277 := by
    have hnat : (2167783527 : ℕ)^8325*50000000000000^6277 ≤ 6581842536701^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167783527 10000000000 6581842536701 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5231917371/10000000000 : ℝ)^8325 ≤ (5293930430029/12500000000000 : ℝ)^6277 := by
    have hnat : (5231917371 : ℕ)^8325*12500000000000^6277 ≤ 5293930430029^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231917371 10000000000 5293930430029 12500000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714714869/5000000000 : ℝ)^8325 ≤ (22242435737769/50000000000000 : ℝ)^6277 := by
    have hnat : (2714714869 : ℕ)^8325*50000000000000^6277 ≤ 22242435737769^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714714869 5000000000 22242435737769 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2167783527/10000000000 : ℝ), (5231917371/10000000000 : ℝ), (2714714869/5000000000 : ℝ)] ![(6581842536701/50000000000000 : ℝ), (5293930430029/12500000000000 : ℝ), (22242435737769/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2167783527/10000000000 : ℝ)|^8325 ≤ (6581842536701/50000000000000 : ℝ)^6277
        have hw : |(-2167783527/10000000000 : ℝ)|=(2167783527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5231917371/10000000000 : ℝ)|^8325 ≤ (5293930430029/12500000000000 : ℝ)^6277
        have hw : |(5231917371/10000000000 : ℝ)|=(5231917371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714714869/5000000000 : ℝ)|^8325 ≤ (22242435737769/50000000000000 : ℝ)^6277
        have hw : |(2714714869/5000000000 : ℝ)|=(2714714869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s3_5 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (530363711/1000000000 : ℝ)*x 0 + (-207125589/1000000000 : ℝ)*x 1 + (1357357491/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530363711/1000000000 : ℝ)^8325 ≤ (43123137765397/100000000000000 : ℝ)^6277 := by
    have hnat : (530363711 : ℕ)^8325*100000000000000^6277 ≤ 43123137765397^6277*1000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530363711 1000000000 43123137765397 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207125589/1000000000 : ℝ)^8325 ≤ (3097997073251/25000000000000 : ℝ)^6277 := by
    have hnat : (207125589 : ℕ)^8325*25000000000000^6277 ≤ 3097997073251^6277*1000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207125589 1000000000 3097997073251 25000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357357491/2500000000 : ℝ)^8325 ≤ (4448487393137/10000000000000 : ℝ)^6277 := by
    have hnat : (1357357491 : ℕ)^8325*10000000000000^6277 ≤ 4448487393137^6277*2500000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357357491 2500000000 4448487393137 10000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530363711/1000000000 : ℝ), (-207125589/1000000000 : ℝ), (1357357491/2500000000 : ℝ)] ![(43123137765397/100000000000000 : ℝ), (3097997073251/25000000000000 : ℝ), (4448487393137/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530363711/1000000000 : ℝ)|^8325 ≤ (43123137765397/100000000000000 : ℝ)^6277
        have hw : |(530363711/1000000000 : ℝ)|=(530363711/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-207125589/1000000000 : ℝ)|^8325 ≤ (3097997073251/25000000000000 : ℝ)^6277
        have hw : |(-207125589/1000000000 : ℝ)|=(207125589/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357357491/2500000000 : ℝ)|^8325 ≤ (4448487393137/10000000000000 : ℝ)^6277
        have hw : |(1357357491/2500000000 : ℝ)|=(1357357491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s3_6 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5303636971/10000000000 : ℝ)*x 0 + (108588603/200000000 : ℝ)*x 1 + (-129453489/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303636971/10000000000 : ℝ)^8325 ≤ (43123136266459/100000000000000 : ℝ)^6277 := by
    have hnat : (5303636971 : ℕ)^8325*100000000000000^6277 ≤ 43123136266459^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303636971 10000000000 43123136266459 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108588603/200000000 : ℝ)^8325 ≤ (22242437976271/50000000000000 : ℝ)^6277 := by
    have hnat : (108588603 : ℕ)^8325*50000000000000^6277 ≤ 22242437976271^6277*200000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108588603 200000000 22242437976271 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (129453489/625000000 : ℝ)^8325 ≤ (12391987769303/100000000000000 : ℝ)^6277 := by
    have hnat : (129453489 : ℕ)^8325*100000000000000^6277 ≤ 12391987769303^6277*625000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129453489 625000000 12391987769303 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303636971/10000000000 : ℝ), (108588603/200000000 : ℝ), (-129453489/625000000 : ℝ)] ![(43123136266459/100000000000000 : ℝ), (22242437976271/50000000000000 : ℝ), (12391987769303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303636971/10000000000 : ℝ)|^8325 ≤ (43123136266459/100000000000000 : ℝ)^6277
        have hw : |(5303636971/10000000000 : ℝ)|=(5303636971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108588603/200000000 : ℝ)|^8325 ≤ (22242437976271/50000000000000 : ℝ)^6277
        have hw : |(108588603/200000000 : ℝ)|=(108588603/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-129453489/625000000 : ℝ)|^8325 ≤ (12391987769303/100000000000000 : ℝ)^6277
        have hw : |(-129453489/625000000 : ℝ)|=(129453489/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s3_7 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4363798561/10000000000 : ℝ)*x 0 + (2282155811/5000000000 : ℝ)*x 1 + (4172135909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363798561/10000000000 : ℝ)^8325 ≤ (33293784528269/100000000000000 : ℝ)^6277 := by
    have hnat : (4363798561 : ℕ)^8325*100000000000000^6277 ≤ 33293784528269^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363798561 10000000000 33293784528269 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2282155811/5000000000 : ℝ)^8325 ≤ (883444959417/2500000000000 : ℝ)^6277 := by
    have hnat : (2282155811 : ℕ)^8325*2500000000000^6277 ≤ 883444959417^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2282155811 5000000000 883444959417 2500000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172135909/10000000000 : ℝ)^8325 ≤ (15684208538963/50000000000000 : ℝ)^6277 := by
    have hnat : (4172135909 : ℕ)^8325*50000000000000^6277 ≤ 15684208538963^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172135909 10000000000 15684208538963 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363798561/10000000000 : ℝ), (2282155811/5000000000 : ℝ), (4172135909/10000000000 : ℝ)] ![(33293784528269/100000000000000 : ℝ), (883444959417/2500000000000 : ℝ), (15684208538963/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363798561/10000000000 : ℝ)|^8325 ≤ (33293784528269/100000000000000 : ℝ)^6277
        have hw : |(4363798561/10000000000 : ℝ)|=(4363798561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2282155811/5000000000 : ℝ)|^8325 ≤ (883444959417/2500000000000 : ℝ)^6277
        have hw : |(2282155811/5000000000 : ℝ)|=(2282155811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172135909/10000000000 : ℝ)|^8325 ≤ (15684208538963/50000000000000 : ℝ)^6277
        have hw : |(4172135909/10000000000 : ℝ)|=(4172135909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1132_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149278633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4133/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (361/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (2121/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7409/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4133/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (361/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4133/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (361/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4133/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (361/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4133/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (361/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4133/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (361/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4133/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (361/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (361/4000 : ℝ) ^ (2081/512 : ℝ) ≤ (1420378727731053/25000000000000000000 : ℝ) := by
    have hpowers : (361/4000 : ℝ)^2081 ≤ (1420378727731053/25000000000000000000 : ℝ)^512 := by
      have hnat : (361 : ℕ)^2081*25000000000000000000^512 ≤ 1420378727731053^512*4000^2081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        361 4000 1420378727731053 25000000000000000000 2081 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (361/4000 : ℝ)) (X := (1420378727731053/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hpowhi : (4133/25000 : ℝ) ^ (2081/512 : ℝ) ≤ (6651509497225743/10000000000000000000 : ℝ) := by
    have hpowers : (4133/25000 : ℝ)^2081 ≤ (6651509497225743/10000000000000000000 : ℝ)^512 := by
      have hnat : (4133 : ℕ)^2081*10000000000000000000^512 ≤ 6651509497225743^512*25000^2081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4133 25000 6651509497225743 10000000000000000000 2081 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4133/25000 : ℝ)) (X := (6651509497225743/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501420378727731053/12500000000000000000 : ℝ) ≤ (5000139779482641/5000000000000000 : ℝ) ^ (2081/512 : ℝ) := by
    have hpowers : (12501420378727731053/12500000000000000000 : ℝ)^512 ≤ (5000139779482641/5000000000000000 : ℝ)^2081 := by
      have hnat : (12501420378727731053 : ℕ)^512*5000000000000000^2081 ≤ 5000139779482641^2081*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501420378727731053 12500000000000000000 5000139779482641 5000000000000000 512 2081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000139779482641/5000000000000000 : ℝ)) (X := (12501420378727731053/12500000000000000000 : ℝ)) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50036098304941590821/50000000000000000000 : ℝ) ≤ (5000887905043051/5000000000000000 : ℝ) ^ (2081/512 : ℝ) := by
    have hpowers : (50036098304941590821/50000000000000000000 : ℝ)^512 ≤ (5000887905043051/5000000000000000 : ℝ)^2081 := by
      have hnat : (50036098304941590821 : ℕ)^512*5000000000000000^2081 ≤ 5000887905043051^2081*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036098304941590821 50000000000000000000 5000887905043051 5000000000000000 512 2081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000887905043051/5000000000000000 : ℝ)) (X := (50036098304941590821/50000000000000000000 : ℝ)) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (5006651509497225743/5000000000000000000 : ℝ) ≤ (5001636030603461/5000000000000000 : ℝ) ^ (2081/512 : ℝ) := by
    have hpowers : (5006651509497225743/5000000000000000000 : ℝ)^512 ≤ (5001636030603461/5000000000000000 : ℝ)^2081 := by
      have hnat : (5006651509497225743 : ℕ)^512*5000000000000000^2081 ≤ 5001636030603461^2081*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5006651509497225743 5000000000000000000 5001636030603461 5000000000000000 512 2081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001636030603461/5000000000000000 : ℝ)) (X := (5006651509497225743/5000000000000000000 : ℝ)) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1420378727731053/25000000000000000000 : ℝ) ≤ ((37522545658210785487/37535000000000000000 : ℝ)+2*(74812556041/37535000000000 : ℝ)*(361/4000 : ℝ))^(2081/512 : ℝ) := by
    rw [show (37522545658210785487/37535000000000000000 : ℝ)+2*(74812556041/37535000000000 : ℝ)*(361/4000 : ℝ)=(5000139779482641/5000000000000000 : ℝ) by norm_num, show 1+2*(1420378727731053/25000000000000000000 : ℝ)=(12501420378727731053/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6651509497225743/10000000000000000000 : ℝ)+(1420378727731053/25000000000000000000 : ℝ) ≤ ((37522545658210785487/37535000000000000000 : ℝ)+(74812556041/37535000000000 : ℝ)*((4133/25000 : ℝ)+(361/4000 : ℝ)))^(2081/512 : ℝ) := by
    rw [show (37522545658210785487/37535000000000000000 : ℝ)+(74812556041/37535000000000 : ℝ)*((4133/25000 : ℝ)+(361/4000 : ℝ))=(5000887905043051/5000000000000000 : ℝ) by norm_num, show 1+(6651509497225743/10000000000000000000 : ℝ)+(1420378727731053/25000000000000000000 : ℝ)=(50036098304941590821/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6651509497225743/10000000000000000000 : ℝ) ≤ ((37522545658210785487/37535000000000000000 : ℝ)+2*(74812556041/37535000000000 : ℝ)*(4133/25000 : ℝ))^(2081/512 : ℝ) := by
    rw [show (37522545658210785487/37535000000000000000 : ℝ)+2*(74812556041/37535000000000 : ℝ)*(4133/25000 : ℝ)=(5001636030603461/5000000000000000 : ℝ) by norm_num, show 1+2*(6651509497225743/10000000000000000000 : ℝ)=(5006651509497225743/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (37522545658210785487/37535000000000000000 : ℝ)*(X 1 0+X 2 0)+(74812556041/37535000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2081/512 : ℝ)) (lo := (361/4000 : ℝ)) (hi := (4133/25000 : ℝ)) (c := (37522545658210785487/37535000000000000000 : ℝ)) (alpha := (74812556041/37535000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (37522545658210785487/37535000000000000000 : ℝ)*(X 0 1+X 2 1)+(74812556041/37535000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2081/512 : ℝ)) (lo := (361/4000 : ℝ)) (hi := (4133/25000 : ℝ)) (c := (37522545658210785487/37535000000000000000 : ℝ)) (alpha := (74812556041/37535000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (37522545658210785487/37535000000000000000 : ℝ)*(X 0 2+X 1 2)+(74812556041/37535000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2081/512 : ℝ)) (lo := (361/4000 : ℝ)) (hi := (4133/25000 : ℝ)) (c := (37522545658210785487/37535000000000000000 : ℝ)) (alpha := (74812556041/37535000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-541941239/2500000000 : ℝ)*X 0 0+(2715106063/5000000000 : ℝ)*X 0 1+(32694621/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((107080687/200000000 : ℝ)*X 1 0+(-2269546557/10000000000 : ℝ)*X 1 1+(1307784809/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((133850861/250000000 : ℝ)*X 2 0+(5231139331/10000000000 : ℝ)*X 2 1+(-283693289/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((872752341/2000000000 : ℝ)*X 0 0+(2085291441/5000000000 : ℝ)*X 0 1+(4565855931/10000000000 : ℝ)*X 0 2+(872752341/2000000000 : ℝ)*X 1 0+(2085291441/5000000000 : ℝ)*X 1 1+(4565855931/10000000000 : ℝ)*X 1 2+(872752341/2000000000 : ℝ)*X 2 0+(2085291441/5000000000 : ℝ)*X 2 1+(4565855931/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2167783527/10000000000 : ℝ)*X 0 0+(5231917371/10000000000 : ℝ)*X 0 1+(2714714869/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530363711/1000000000 : ℝ)*X 1 0+(-207125589/1000000000 : ℝ)*X 1 1+(1357357491/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5303636971/10000000000 : ℝ)*X 2 0+(108588603/200000000 : ℝ)*X 2 1+(-129453489/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4363798561/10000000000 : ℝ)*X 0 0+(2282155811/5000000000 : ℝ)*X 0 1+(4172135909/10000000000 : ℝ)*X 0 2+(4363798561/10000000000 : ℝ)*X 1 0+(2282155811/5000000000 : ℝ)*X 1 1+(4172135909/10000000000 : ℝ)*X 1 2+(4363798561/10000000000 : ℝ)*X 2 0+(2282155811/5000000000 : ℝ)*X 2 1+(4172135909/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (51132916900257874189893/7507000000000000000000000000 : ℝ) := by norm_num
    linear_combination (110518671/6250000000000 : ℝ)*(base19) + (1668482857/100000000000000 : ℝ)*(base23) + (12331489/12500000000000 : ℝ)*(lower2) + (18619977/20000000000000 : ℝ)*(upper3) + (224219287/100000000000000 : ℝ)*(upper5) + (1888319354085083/50000000000000 : ℝ)*(major0) + (1888319354085083/50000000000000 : ℝ)*(major1) + (1888319354085083/50000000000000 : ℝ)*(major2) + (1255829164877177/25000000000000 : ℝ)*(sp0) + (100466991642639/2000000000000 : ℝ)*(sp1) + (5023349681947829/100000000000000 : ℝ)*(sp2) + (632477906131943/25000000000000 : ℝ)*(sp3) + (17345460989/50000000000000 : ℝ)*(sp4) + (2842867273/20000000000000 : ℝ)*(sp7) + (316240729858017/12500000000000 : ℝ)*(f.failure) + (2511675675215343/50000000000000 : ℝ)*(f.sum) + (6166263767327/7507000000000000000000000000 : ℝ)*base65 + (4632923577097590421/1876750000000000000000000000000000 : ℝ)*base67 + (5644101583344159579/1876750000000000000000000000000000 : ℝ)*base70 + (799814572768840421/1876750000000000000000000000000000 : ℝ)*base71 + (3030682731717/938375000000000000000000000 : ℝ)*base73 + (27229844908567159579/1876750000000000000000000000000000 : ℝ)*base76 + (7900032275813840421/1876750000000000000000000000000000 : ℝ)*base77 + (27053915766145159579/1876750000000000000000000000000000 : ℝ)*base80 + (8911103555359/7507000000000000000000000000 : ℝ)*base82 + (13149239/1250000000000000000000 : ℝ)*base90 + (13149239/1250000000000000000000 : ℝ)*base92 + (13149239/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19574238160065216573537/1876750000000000000000000000 : ℝ) := by norm_num
    linear_combination (964911637/50000000000000 : ℝ)*(base19) + (2103861301/100000000000000 : ℝ)*(base23) + (289730179/100000000000000 : ℝ)*(upper3) + (24118753/20000000000000 : ℝ)*(lower4) + (85641029/50000000000000 : ℝ)*(upper5) + (1903211511916553/50000000000000 : ℝ)*(major0) + (1903211511916553/50000000000000 : ℝ)*(major1) + (1903211511916553/50000000000000 : ℝ)*(major2) + (891030231/2500000000000 : ℝ)*(sp1) + (68736949/156250000000 : ℝ)*(sp2) + (1265741924621673/25000000000000 : ℝ)*(sp4) + (2531465063727089/50000000000000 : ℝ)*(sp5) + (316432600186127/6250000000000 : ℝ)*(sp6) + (1274939000758771/50000000000000 : ℝ)*(sp7) + (1274939000758771/50000000000000 : ℝ)*(f.failure) + (1265741924621673/25000000000000 : ℝ)*(f.sum) + (14699715101131/3753500000000000000000000000 : ℝ)*base66 + (11572217877852466311/1876750000000000000000000000000000 : ℝ)*base67 + (3983717177804033689/1876750000000000000000000000000000 : ℝ)*base70 + (16439012009726966311/1876750000000000000000000000000000 : ℝ)*base71 + (1028453140451/469187500000000000000000000 : ℝ)*base73 + (29841360103992033689/1876750000000000000000000000000000 : ℝ)*base76 + (2873187582415966311/1876750000000000000000000000000000 : ℝ)*base77 + (12487068194546533689/1876750000000000000000000000000000 : ℝ)*base80 + (13806290900727/3753500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2359957/5000000000000000000000 : ℝ)*base90 + (2359957/5000000000000000000000 : ℝ)*base92 + (2359957/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1132_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149278633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4133/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (361/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2121/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7409/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1132_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1132_s4_0 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-217084577/1000000000 : ℝ)*x 0 + (168824353/312500000 : ℝ)*x 1 + (5256957337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217084577/1000000000 : ℝ)^8325 ≤ (13188353041311/100000000000000 : ℝ)^6277 := by
    have hnat : (217084577 : ℕ)^8325*100000000000000^6277 ≤ 13188353041311^6277*1000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217084577 1000000000 13188353041311 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168824353/312500000 : ℝ)^8325 ≤ (44191166650823/100000000000000 : ℝ)^6277 := by
    have hnat : (168824353 : ℕ)^8325*100000000000000^6277 ≤ 44191166650823^6277*312500000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168824353 312500000 44191166650823 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5256957337/10000000000 : ℝ)^8325 ≤ (42620480293753/100000000000000 : ℝ)^6277 := by
    have hnat : (5256957337 : ℕ)^8325*100000000000000^6277 ≤ 42620480293753^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256957337 10000000000 42620480293753 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-217084577/1000000000 : ℝ), (168824353/312500000 : ℝ), (5256957337/10000000000 : ℝ)] ![(13188353041311/100000000000000 : ℝ), (44191166650823/100000000000000 : ℝ), (42620480293753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-217084577/1000000000 : ℝ)|^8325 ≤ (13188353041311/100000000000000 : ℝ)^6277
        have hw : |(-217084577/1000000000 : ℝ)|=(217084577/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168824353/312500000 : ℝ)|^8325 ≤ (44191166650823/100000000000000 : ℝ)^6277
        have hw : |(168824353/312500000 : ℝ)|=(168824353/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5256957337/10000000000 : ℝ)|^8325 ≤ (42620480293753/100000000000000 : ℝ)^6277
        have hw : |(5256957337/10000000000 : ℝ)|=(5256957337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s4_1 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5347090807/10000000000 : ℝ)*x 0 + (-35074319/156250000 : ℝ)*x 1 + (5256957561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347090807/10000000000 : ℝ)^8325 ≤ (43592355506971/100000000000000 : ℝ)^6277 := by
    have hnat : (5347090807 : ℕ)^8325*100000000000000^6277 ≤ 43592355506971^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347090807 10000000000 43592355506971 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35074319/156250000 : ℝ)^8325 ≤ (1378716177909/10000000000000 : ℝ)^6277 := by
    have hnat : (35074319 : ℕ)^8325*10000000000000^6277 ≤ 1378716177909^6277*156250000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35074319 156250000 1378716177909 10000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5256957561/10000000000 : ℝ)^8325 ≤ (42620482702349/100000000000000 : ℝ)^6277 := by
    have hnat : (5256957561 : ℕ)^8325*100000000000000^6277 ≤ 42620482702349^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256957561 10000000000 42620482702349 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347090807/10000000000 : ℝ), (-35074319/156250000 : ℝ), (5256957561/10000000000 : ℝ)] ![(43592355506971/100000000000000 : ℝ), (1378716177909/10000000000000 : ℝ), (42620482702349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347090807/10000000000 : ℝ)|^8325 ≤ (43592355506971/100000000000000 : ℝ)^6277
        have hw : |(5347090807/10000000000 : ℝ)|=(5347090807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-35074319/156250000 : ℝ)|^8325 ≤ (1378716177909/10000000000000 : ℝ)^6277
        have hw : |(-35074319/156250000 : ℝ)|=(35074319/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5256957561/10000000000 : ℝ)|^8325 ≤ (42620482702349/100000000000000 : ℝ)^6277
        have hw : |(5256957561/10000000000 : ℝ)|=(5256957561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s4_2 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5347091419/10000000000 : ℝ)*x 0 + (2628478373/5000000000 : ℝ)*x 1 + (-1122378339/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347091419/10000000000 : ℝ)^8325 ≤ (21796181062101/50000000000000 : ℝ)^6277 := by
    have hnat : (5347091419 : ℕ)^8325*50000000000000^6277 ≤ 21796181062101^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347091419 10000000000 21796181062101 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2628478373/5000000000 : ℝ)^8325 ≤ (42620473938929/100000000000000 : ℝ)^6277 := by
    have hnat : (2628478373 : ℕ)^8325*100000000000000^6277 ≤ 42620473938929^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628478373 5000000000 42620473938929 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1122378339/5000000000 : ℝ)^8325 ≤ (13787163913309/100000000000000 : ℝ)^6277 := by
    have hnat : (1122378339 : ℕ)^8325*100000000000000^6277 ≤ 13787163913309^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122378339 5000000000 13787163913309 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347091419/10000000000 : ℝ), (2628478373/5000000000 : ℝ), (-1122378339/5000000000 : ℝ)] ![(21796181062101/50000000000000 : ℝ), (42620473938929/100000000000000 : ℝ), (13787163913309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347091419/10000000000 : ℝ)|^8325 ≤ (21796181062101/50000000000000 : ℝ)^6277
        have hw : |(5347091419/10000000000 : ℝ)|=(5347091419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2628478373/5000000000 : ℝ)|^8325 ≤ (42620473938929/100000000000000 : ℝ)^6277
        have hw : |(2628478373/5000000000 : ℝ)|=(2628478373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1122378339/5000000000 : ℝ)|^8325 ≤ (13787163913309/100000000000000 : ℝ)^6277
        have hw : |(-1122378339/5000000000 : ℝ)|=(1122378339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s4_3 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4365600839/10000000000 : ℝ)*x 0 + (2111803349/5000000000 : ℝ)*x 1 + (2256177211/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4365600839/10000000000 : ℝ)^8325 ≤ (33312022713493/100000000000000 : ℝ)^6277 := by
    have hnat : (4365600839 : ℕ)^8325*100000000000000^6277 ≤ 33312022713493^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365600839 10000000000 33312022713493 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2111803349/5000000000 : ℝ)^8325 ≤ (3188269497501/10000000000000 : ℝ)^6277 := by
    have hnat : (2111803349 : ℕ)^8325*10000000000000^6277 ≤ 3188269497501^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111803349 5000000000 3188269497501 10000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2256177211/5000000000 : ℝ)^8325 ≤ (17402641145421/50000000000000 : ℝ)^6277 := by
    have hnat : (2256177211 : ℕ)^8325*50000000000000^6277 ≤ 17402641145421^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2256177211 5000000000 17402641145421 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4365600839/10000000000 : ℝ), (2111803349/5000000000 : ℝ), (2256177211/5000000000 : ℝ)] ![(33312022713493/100000000000000 : ℝ), (3188269497501/10000000000000 : ℝ), (17402641145421/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4365600839/10000000000 : ℝ)|^8325 ≤ (33312022713493/100000000000000 : ℝ)^6277
        have hw : |(4365600839/10000000000 : ℝ)|=(4365600839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2111803349/5000000000 : ℝ)|^8325 ≤ (3188269497501/10000000000000 : ℝ)^6277
        have hw : |(2111803349/5000000000 : ℝ)|=(2111803349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2256177211/5000000000 : ℝ)|^8325 ≤ (17402641145421/50000000000000 : ℝ)^6277
        have hw : |(2256177211/5000000000 : ℝ)|=(2256177211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s4_4 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-542713449/2500000000 : ℝ)*x 0 + (2628686229/5000000000 : ℝ)*x 1 + (5401961883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542713449/2500000000 : ℝ)^8325 ≤ (6594208854931/50000000000000 : ℝ)^6277 := by
    have hnat : (542713449 : ℕ)^8325*50000000000000^6277 ≤ 6594208854931^6277*2500000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542713449 2500000000 6594208854931 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2628686229/5000000000 : ℝ)^8325 ≤ (21312472003559/50000000000000 : ℝ)^6277 := by
    have hnat : (2628686229 : ℕ)^8325*50000000000000^6277 ≤ 21312472003559^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628686229 5000000000 21312472003559 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5401961883/10000000000 : ℝ)^8325 ≤ (44186638269351/100000000000000 : ℝ)^6277 := by
    have hnat : (5401961883 : ℕ)^8325*100000000000000^6277 ≤ 44186638269351^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401961883 10000000000 44186638269351 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-542713449/2500000000 : ℝ), (2628686229/5000000000 : ℝ), (5401961883/10000000000 : ℝ)] ![(6594208854931/50000000000000 : ℝ), (21312472003559/50000000000000 : ℝ), (44186638269351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-542713449/2500000000 : ℝ)|^8325 ≤ (6594208854931/50000000000000 : ℝ)^6277
        have hw : |(-542713449/2500000000 : ℝ)|=(542713449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2628686229/5000000000 : ℝ)|^8325 ≤ (21312472003559/50000000000000 : ℝ)^6277
        have hw : |(2628686229/5000000000 : ℝ)|=(2628686229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5401961883/10000000000 : ℝ)|^8325 ≤ (44186638269351/100000000000000 : ℝ)^6277
        have hw : |(5401961883/10000000000 : ℝ)|=(5401961883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s4_5 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (331892329/625000000 : ℝ)*x 0 + (-2099751377/10000000000 : ℝ)*x 1 + (108039241/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331892329/625000000 : ℝ)^8325 ≤ (43194757958403/100000000000000 : ℝ)^6277 := by
    have hnat : (331892329 : ℕ)^8325*100000000000000^6277 ≤ 43194757958403^6277*625000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331892329 625000000 43194757958403 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2099751377/10000000000 : ℝ)^8325 ≤ (6309300970831/50000000000000 : ℝ)^6277 := by
    have hnat : (2099751377 : ℕ)^8325*50000000000000^6277 ≤ 6309300970831^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099751377 10000000000 6309300970831 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108039241/200000000 : ℝ)^8325 ≤ (22093320040529/50000000000000 : ℝ)^6277 := by
    have hnat : (108039241 : ℕ)^8325*50000000000000^6277 ≤ 22093320040529^6277*200000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108039241 200000000 22093320040529 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331892329/625000000 : ℝ), (-2099751377/10000000000 : ℝ), (108039241/200000000 : ℝ)] ![(43194757958403/100000000000000 : ℝ), (6309300970831/50000000000000 : ℝ), (22093320040529/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331892329/625000000 : ℝ)|^8325 ≤ (43194757958403/100000000000000 : ℝ)^6277
        have hw : |(331892329/625000000 : ℝ)|=(331892329/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2099751377/10000000000 : ℝ)|^8325 ≤ (6309300970831/50000000000000 : ℝ)^6277
        have hw : |(-2099751377/10000000000 : ℝ)|=(2099751377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(108039241/200000000 : ℝ)|^8325 ≤ (22093320040529/50000000000000 : ℝ)^6277
        have hw : |(108039241/200000000 : ℝ)|=(108039241/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s4_6 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310277443/10000000000 : ℝ)*x 0 + (5401961901/10000000000 : ℝ)*x 1 + (-1049875669/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310277443/10000000000 : ℝ)^8325 ≤ (43194759889477/100000000000000 : ℝ)^6277 := by
    have hnat : (5310277443 : ℕ)^8325*100000000000000^6277 ≤ 43194759889477^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310277443 10000000000 43194759889477 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5401961901/10000000000 : ℝ)^8325 ≤ (353493107717/800000000000 : ℝ)^6277 := by
    have hnat : (5401961901 : ℕ)^8325*800000000000^6277 ≤ 353493107717^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401961901 10000000000 353493107717 800000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049875669/5000000000 : ℝ)^8325 ≤ (12618601630819/100000000000000 : ℝ)^6277 := by
    have hnat : (1049875669 : ℕ)^8325*100000000000000^6277 ≤ 12618601630819^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049875669 5000000000 12618601630819 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310277443/10000000000 : ℝ), (5401961901/10000000000 : ℝ), (-1049875669/5000000000 : ℝ)] ![(43194759889477/100000000000000 : ℝ), (353493107717/800000000000 : ℝ), (12618601630819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310277443/10000000000 : ℝ)|^8325 ≤ (43194759889477/100000000000000 : ℝ)^6277
        have hw : |(5310277443/10000000000 : ℝ)|=(5310277443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5401961901/10000000000 : ℝ)|^8325 ≤ (353493107717/800000000000 : ℝ)^6277
        have hw : |(5401961901/10000000000 : ℝ)|=(5401961901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1049875669/5000000000 : ℝ)|^8325 ≤ (12618601630819/100000000000000 : ℝ)^6277
        have hw : |(-1049875669/5000000000 : ℝ)|=(1049875669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s4_7 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5457019/12500000 : ℝ)*x 0 + (2255764193/5000000000 : ℝ)*x 1 + (4224436183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5457019/12500000 : ℝ)^8325 ≤ (33312168049763/100000000000000 : ℝ)^6277 := by
    have hnat : (5457019 : ℕ)^8325*100000000000000^6277 ≤ 33312168049763^6277*12500000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457019 12500000 33312168049763 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2255764193/5000000000 : ℝ)^8325 ≤ (17398416112677/50000000000000 : ℝ)^6277 := by
    have hnat : (2255764193 : ℕ)^8325*50000000000000^6277 ≤ 17398416112677^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255764193 5000000000 17398416112677 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4224436183/10000000000 : ℝ)^8325 ≤ (1993187482281/6250000000000 : ℝ)^6277 := by
    have hnat : (4224436183 : ℕ)^8325*6250000000000^6277 ≤ 1993187482281^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224436183 10000000000 1993187482281 6250000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5457019/12500000 : ℝ), (2255764193/5000000000 : ℝ), (4224436183/10000000000 : ℝ)] ![(33312168049763/100000000000000 : ℝ), (17398416112677/50000000000000 : ℝ), (1993187482281/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5457019/12500000 : ℝ)|^8325 ≤ (33312168049763/100000000000000 : ℝ)^6277
        have hw : |(5457019/12500000 : ℝ)|=(5457019/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2255764193/5000000000 : ℝ)|^8325 ≤ (17398416112677/50000000000000 : ℝ)^6277
        have hw : |(2255764193/5000000000 : ℝ)|=(2255764193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4224436183/10000000000 : ℝ)|^8325 ≤ (1993187482281/6250000000000 : ℝ)^6277
        have hw : |(4224436183/10000000000 : ℝ)|=(4224436183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1132_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149278633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7409/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2121/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2789/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3559/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7409/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2121/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7409/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2121/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7409/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2121/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7409/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2121/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7409/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2121/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7409/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2121/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2121/20000 : ℝ) ^ (2081/512 : ℝ) ≤ (2189090945549053/20000000000000000000 : ℝ) := by
    have hpowers : (2121/20000 : ℝ)^2081 ≤ (2189090945549053/20000000000000000000 : ℝ)^512 := by
      have hnat : (2121 : ℕ)^2081*20000000000000000000^512 ≤ 2189090945549053^512*20000^2081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2121 20000 2189090945549053 20000000000000000000 2081 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2121/20000 : ℝ)) (X := (2189090945549053/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7409/50000 : ℝ) ^ (2081/512 : ℝ) ≤ (8525957339335461/20000000000000000000 : ℝ) := by
    have hpowers : (7409/50000 : ℝ)^2081 ≤ (8525957339335461/20000000000000000000 : ℝ)^512 := by
      have hnat : (7409 : ℕ)^2081*20000000000000000000^512 ≤ 8525957339335461^512*50000^2081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7409 50000 8525957339335461 20000000000000000000 2081 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7409/50000 : ℝ)) (X := (8525957339335461/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002189090945549053/10000000000000000000 : ℝ) ≤ (10000538549774589/10000000000000000 : ℝ) ^ (2081/512 : ℝ) := by
    have hpowers : (10002189090945549053/10000000000000000000 : ℝ)^512 ≤ (10000538549774589/10000000000000000 : ℝ)^2081 := by
      have hnat : (10002189090945549053 : ℕ)^512*10000000000000000^2081 ≤ 10000538549774589^2081*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002189090945549053 10000000000000000000 10000538549774589 10000000000000000 512 2081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000538549774589/10000000000000000 : ℝ)) (X := (10002189090945549053/10000000000000000000 : ℝ)) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (10005357524142442257/10000000000000000000 : ℝ) ≤ (10001317875311143/10000000000000000 : ℝ) ^ (2081/512 : ℝ) := by
    have hpowers : (10005357524142442257/10000000000000000000 : ℝ)^512 ≤ (10001317875311143/10000000000000000 : ℝ)^2081 := by
      have hnat : (10005357524142442257 : ℕ)^512*10000000000000000^2081 ≤ 10001317875311143^2081*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005357524142442257 10000000000000000000 10001317875311143 10000000000000000 512 2081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001317875311143/10000000000000000 : ℝ)) (X := (10005357524142442257/10000000000000000000 : ℝ)) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10008525957339335461/10000000000000000000 : ℝ) ≤ (10002097200847697/10000000000000000 : ℝ) ^ (2081/512 : ℝ) := by
    have hpowers : (10008525957339335461/10000000000000000000 : ℝ)^512 ≤ (10002097200847697/10000000000000000 : ℝ)^2081 := by
      have hnat : (10008525957339335461 : ℕ)^512*10000000000000000^2081 ≤ 10002097200847697^2081*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10008525957339335461 10000000000000000000 10002097200847697 10000000000000000 512 2081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002097200847697/10000000000000000 : ℝ)) (X := (10008525957339335461/10000000000000000000 : ℝ)) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2189090945549053/20000000000000000000 : ℝ) ≤ ((42115739415570033117/42130000000000000000 : ℝ)+2*(389662768277/210650000000000 : ℝ)*(2121/20000 : ℝ))^(2081/512 : ℝ) := by
    rw [show (42115739415570033117/42130000000000000000 : ℝ)+2*(389662768277/210650000000000 : ℝ)*(2121/20000 : ℝ)=(10000538549774589/10000000000000000 : ℝ) by norm_num, show 1+2*(2189090945549053/20000000000000000000 : ℝ)=(10002189090945549053/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8525957339335461/20000000000000000000 : ℝ)+(2189090945549053/20000000000000000000 : ℝ) ≤ ((42115739415570033117/42130000000000000000 : ℝ)+(389662768277/210650000000000 : ℝ)*((7409/50000 : ℝ)+(2121/20000 : ℝ)))^(2081/512 : ℝ) := by
    rw [show (42115739415570033117/42130000000000000000 : ℝ)+(389662768277/210650000000000 : ℝ)*((7409/50000 : ℝ)+(2121/20000 : ℝ))=(10001317875311143/10000000000000000 : ℝ) by norm_num, show 1+(8525957339335461/20000000000000000000 : ℝ)+(2189090945549053/20000000000000000000 : ℝ)=(10005357524142442257/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8525957339335461/20000000000000000000 : ℝ) ≤ ((42115739415570033117/42130000000000000000 : ℝ)+2*(389662768277/210650000000000 : ℝ)*(7409/50000 : ℝ))^(2081/512 : ℝ) := by
    rw [show (42115739415570033117/42130000000000000000 : ℝ)+2*(389662768277/210650000000000 : ℝ)*(7409/50000 : ℝ)=(10002097200847697/10000000000000000 : ℝ) by norm_num, show 1+2*(8525957339335461/20000000000000000000 : ℝ)=(10008525957339335461/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (42115739415570033117/42130000000000000000 : ℝ)*(X 1 0+X 2 0)+(389662768277/210650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2081/512 : ℝ)) (lo := (2121/20000 : ℝ)) (hi := (7409/50000 : ℝ)) (c := (42115739415570033117/42130000000000000000 : ℝ)) (alpha := (389662768277/210650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (42115739415570033117/42130000000000000000 : ℝ)*(X 0 1+X 2 1)+(389662768277/210650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2081/512 : ℝ)) (lo := (2121/20000 : ℝ)) (hi := (7409/50000 : ℝ)) (c := (42115739415570033117/42130000000000000000 : ℝ)) (alpha := (389662768277/210650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (42115739415570033117/42130000000000000000 : ℝ)*(X 0 2+X 1 2)+(389662768277/210650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2081/512 : ℝ)) (lo := (2121/20000 : ℝ)) (hi := (7409/50000 : ℝ)) (c := (42115739415570033117/42130000000000000000 : ℝ)) (alpha := (389662768277/210650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-217084577/1000000000 : ℝ)*X 0 0+(168824353/312500000 : ℝ)*X 0 1+(5256957337/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347090807/10000000000 : ℝ)*X 1 0+(-35074319/156250000 : ℝ)*X 1 1+(5256957561/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347091419/10000000000 : ℝ)*X 2 0+(2628478373/5000000000 : ℝ)*X 2 1+(-1122378339/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4365600839/10000000000 : ℝ)*X 0 0+(2111803349/5000000000 : ℝ)*X 0 1+(2256177211/5000000000 : ℝ)*X 0 2+(4365600839/10000000000 : ℝ)*X 1 0+(2111803349/5000000000 : ℝ)*X 1 1+(2256177211/5000000000 : ℝ)*X 1 2+(4365600839/10000000000 : ℝ)*X 2 0+(2111803349/5000000000 : ℝ)*X 2 1+(2256177211/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-542713449/2500000000 : ℝ)*X 0 0+(2628686229/5000000000 : ℝ)*X 0 1+(5401961883/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((331892329/625000000 : ℝ)*X 1 0+(-2099751377/10000000000 : ℝ)*X 1 1+(108039241/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310277443/10000000000 : ℝ)*X 2 0+(5401961901/10000000000 : ℝ)*X 2 1+(-1049875669/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((5457019/12500000 : ℝ)*X 0 0+(2255764193/5000000000 : ℝ)*X 0 1+(4224436183/10000000000 : ℝ)*X 0 2+(5457019/12500000 : ℝ)*X 1 0+(2255764193/5000000000 : ℝ)*X 1 1+(4224436183/10000000000 : ℝ)*X 1 2+(5457019/12500000 : ℝ)*X 2 0+(2255764193/5000000000 : ℝ)*X 2 1+(4224436183/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11701990142014747156617/957500000000000000000000000 : ℝ) := by norm_num
    linear_combination (223510629/25000000000000 : ℝ)*(base23) + (610279/250000000000 : ℝ)*(lower2) + (15403439/10000000000000 : ℝ)*(upper3) + (39679113/12500000000000 : ℝ)*(lower4) + (157897589/100000000000000 : ℝ)*(upper5) + (5169893141951373/100000000000000 : ℝ)*(major0) + (5169893141951373/100000000000000 : ℝ)*(major1) + (5169893141951373/100000000000000 : ℝ)*(major2) + (6876535283953761/100000000000000 : ℝ)*(sp0) + (6876535283953761/100000000000000 : ℝ)*(sp1) + (859566251645337/12500000000000 : ℝ)*(sp2) + (432904907114513/12500000000000 : ℝ)*(sp3) + (87534971/2000000000000 : ℝ)*(sp6) + (11335652877/100000000000000 : ℝ)*(sp7) + (173162529628449/5000000000000 : ℝ)*(f.failure) + (6876535283953761/100000000000000 : ℝ)*(f.sum) + (29063593182683/478750000000000000000000000 : ℝ)*base65 + (418538625515256331/383000000000000000000000000000000 : ℝ)*base67 + (2190262605962743669/383000000000000000000000000000000 : ℝ)*base70 + (22734472768336256331/383000000000000000000000000000000 : ℝ)*base71 + (105395470519/239375000000000000000000000 : ℝ)*base73 + (3571223669674743669/383000000000000000000000000000000 : ℝ)*base76 + (702670408035256331/383000000000000000000000000000000 : ℝ)*base77 + (3963750633814743669/383000000000000000000000000000000 : ℝ)*base80 + (4023360727343/1915000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (369783/500000000000000000000 : ℝ)*base90 + (369783/500000000000000000000 : ℝ)*base92 + (369783/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (186187648821805683472119/21065000000000000000000000000 : ℝ) := by norm_num
    linear_combination (399535179/20000000000000 : ℝ)*(base19) + (2229213749/100000000000000 : ℝ)*(base23) + (1779953/20000000000000 : ℝ)*(upper2) + (51081373/20000000000000 : ℝ)*(upper3) + (436747887/100000000000000 : ℝ)*(upper5) + (1299918030614229/25000000000000 : ℝ)*(major0) + (1299918030614229/25000000000000 : ℝ)*(major1) + (1299918030614229/25000000000000 : ℝ)*(major2) + (26848538091/50000000000000 : ℝ)*(sp1) + (25524581513/50000000000000 : ℝ)*(sp2) + (216129524032081/3125000000000 : ℝ)*(sp4) + (1383217814854903/20000000000000 : ℝ)*(sp5) + (864511436331227/12500000000000 : ℝ)*(sp6) + (870799795315803/25000000000000 : ℝ)*(sp7) + (870799795315803/25000000000000 : ℝ)*(f.failure) + (216129524032081/3125000000000 : ℝ)*(f.sum) + (3202424179193/2633125000000000000000000000 : ℝ)*base65 + (7840326949977978207/1053250000000000000000000000000000 : ℝ)*base68 + (6622424333739021793/1053250000000000000000000000000000 : ℝ)*base69 + (1464010595607521793/1053250000000000000000000000000000 : ℝ)*base71 + (44512259169739/21065000000000000000000000000 : ℝ)*base73 + (4829220732187978207/1053250000000000000000000000000000 : ℝ)*base76 + (4704240957426521793/1053250000000000000000000000000000 : ℝ)*base77 + (2256764823824978207/1053250000000000000000000000000000 : ℝ)*base80 + (521526578379/1316562500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (24862701/2500000000000000000000 : ℝ)*base90 + (24862701/2500000000000000000000 : ℝ)*base92 + (24862701/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1132_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149278633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7409/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2121/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2789/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1132_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1132_s5_0 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2171505883/10000000000 : ℝ)*x 0 + (1348795323/2500000000 : ℝ)*x 1 + (131593051/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171505883/10000000000 : ℝ)^8325 ≤ (3298418021183/25000000000000 : ℝ)^6277 := by
    have hnat : (2171505883 : ℕ)^8325*25000000000000^6277 ≤ 3298418021183^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171505883 10000000000 3298418021183 25000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348795323/2500000000 : ℝ)^8325 ≤ (44113093778721/100000000000000 : ℝ)^6277 := by
    have hnat : (1348795323 : ℕ)^8325*100000000000000^6277 ≤ 44113093778721^6277*2500000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348795323 2500000000 44113093778721 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131593051/250000000 : ℝ)^8325 ≤ (8538646824967/20000000000000 : ℝ)^6277 := by
    have hnat : (131593051 : ℕ)^8325*20000000000000^6277 ≤ 8538646824967^6277*250000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131593051 250000000 8538646824967 20000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2171505883/10000000000 : ℝ), (1348795323/2500000000 : ℝ), (131593051/250000000 : ℝ)] ![(3298418021183/25000000000000 : ℝ), (44113093778721/100000000000000 : ℝ), (8538646824967/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2171505883/10000000000 : ℝ)|^8325 ≤ (3298418021183/25000000000000 : ℝ)^6277
        have hw : |(-2171505883/10000000000 : ℝ)|=(2171505883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348795323/2500000000 : ℝ)|^8325 ≤ (44113093778721/100000000000000 : ℝ)^6277
        have hw : |(1348795323/2500000000 : ℝ)|=(1348795323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131593051/250000000 : ℝ)|^8325 ≤ (8538646824967/20000000000000 : ℝ)^6277
        have hw : |(131593051/250000000 : ℝ)|=(131593051/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s5_1 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (83520119/156250000 : ℝ)*x 0 + (-1119107783/5000000000 : ℝ)*x 1 + (1052744409/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83520119/156250000 : ℝ)^8325 ≤ (43572859632177/100000000000000 : ℝ)^6277 := by
    have hnat : (83520119 : ℕ)^8325*100000000000000^6277 ≤ 43572859632177^6277*156250000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83520119 156250000 43572859632177 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1119107783/5000000000 : ℝ)^8325 ≤ (13733906173529/100000000000000 : ℝ)^6277 := by
    have hnat : (1119107783 : ℕ)^8325*100000000000000^6277 ≤ 13733906173529^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119107783 5000000000 13733906173529 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052744409/2000000000 : ℝ)^8325 ≤ (42693234178621/100000000000000 : ℝ)^6277 := by
    have hnat : (1052744409 : ℕ)^8325*100000000000000^6277 ≤ 42693234178621^6277*2000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052744409 2000000000 42693234178621 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83520119/156250000 : ℝ), (-1119107783/5000000000 : ℝ), (1052744409/2000000000 : ℝ)] ![(43572859632177/100000000000000 : ℝ), (13733906173529/100000000000000 : ℝ), (42693234178621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83520119/156250000 : ℝ)|^8325 ≤ (43572859632177/100000000000000 : ℝ)^6277
        have hw : |(83520119/156250000 : ℝ)|=(83520119/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1119107783/5000000000 : ℝ)|^8325 ≤ (13733906173529/100000000000000 : ℝ)^6277
        have hw : |(-1119107783/5000000000 : ℝ)|=(1119107783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052744409/2000000000 : ℝ)|^8325 ≤ (42693234178621/100000000000000 : ℝ)^6277
        have hw : |(1052744409/2000000000 : ℝ)|=(1052744409/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s5_2 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672643933/5000000000 : ℝ)*x 0 + (2631860917/5000000000 : ℝ)*x 1 + (-279776939/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672643933/5000000000 : ℝ)^8325 ≤ (43572862334997/100000000000000 : ℝ)^6277 := by
    have hnat : (2672643933 : ℕ)^8325*100000000000000^6277 ≤ 43572862334997^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672643933 5000000000 43572862334997 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631860917/5000000000 : ℝ)^8325 ≤ (42693231908857/100000000000000 : ℝ)^6277 := by
    have hnat : (2631860917 : ℕ)^8325*100000000000000^6277 ≤ 42693231908857^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631860917 5000000000 42693231908857 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (279776939/1250000000 : ℝ)^8325 ≤ (1373390573407/10000000000000 : ℝ)^6277 := by
    have hnat : (279776939 : ℕ)^8325*10000000000000^6277 ≤ 1373390573407^6277*1250000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279776939 1250000000 1373390573407 10000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672643933/5000000000 : ℝ), (2631860917/5000000000 : ℝ), (-279776939/1250000000 : ℝ)] ![(43572862334997/100000000000000 : ℝ), (42693231908857/100000000000000 : ℝ), (1373390573407/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672643933/5000000000 : ℝ)|^8325 ≤ (43572862334997/100000000000000 : ℝ)^6277
        have hw : |(2672643933/5000000000 : ℝ)|=(2672643933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631860917/5000000000 : ℝ)|^8325 ≤ (42693231908857/100000000000000 : ℝ)^6277
        have hw : |(2631860917/5000000000 : ℝ)|=(2631860917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-279776939/1250000000 : ℝ)|^8325 ≤ (1373390573407/10000000000000 : ℝ)^6277
        have hw : |(-279776939/1250000000 : ℝ)|=(279776939/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s5_3 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (545748161/1250000000 : ℝ)*x 0 + (4237419617/10000000000 : ℝ)*x 1 + (2249220901/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545748161/1250000000 : ℝ)^8325 ≤ (16657956735069/50000000000000 : ℝ)^6277 := by
    have hnat : (545748161 : ℕ)^8325*50000000000000^6277 ≤ 16657956735069^6277*1250000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545748161 1250000000 16657956735069 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4237419617/10000000000 : ℝ)^8325 ≤ (16010529088777/50000000000000 : ℝ)^6277 := by
    have hnat : (4237419617 : ℕ)^8325*50000000000000^6277 ≤ 16010529088777^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237419617 10000000000 16010529088777 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2249220901/5000000000 : ℝ)^8325 ≤ (34663028337681/100000000000000 : ℝ)^6277 := by
    have hnat : (2249220901 : ℕ)^8325*100000000000000^6277 ≤ 34663028337681^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249220901 5000000000 34663028337681 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(545748161/1250000000 : ℝ), (4237419617/10000000000 : ℝ), (2249220901/5000000000 : ℝ)] ![(16657956735069/50000000000000 : ℝ), (16010529088777/50000000000000 : ℝ), (34663028337681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(545748161/1250000000 : ℝ)|^8325 ≤ (16657956735069/50000000000000 : ℝ)^6277
        have hw : |(545748161/1250000000 : ℝ)|=(545748161/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4237419617/10000000000 : ℝ)|^8325 ≤ (16010529088777/50000000000000 : ℝ)^6277
        have hw : |(4237419617/10000000000 : ℝ)|=(4237419617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2249220901/5000000000 : ℝ)|^8325 ≤ (34663028337681/100000000000000 : ℝ)^6277
        have hw : |(2249220901/5000000000 : ℝ)|=(2249220901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s5_4 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-217151139/1000000000 : ℝ)*x 0 + (526406193/1000000000 : ℝ)*x 1 + (5394840027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217151139/1000000000 : ℝ)^8325 ≤ (1319371646113/10000000000000 : ℝ)^6277 := by
    have hnat : (217151139 : ℕ)^8325*10000000000000^6277 ≤ 1319371646113^6277*1000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217151139 1000000000 1319371646113 10000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526406193/1000000000 : ℝ)^8325 ≤ (42696890419451/100000000000000 : ℝ)^6277 := by
    have hnat : (526406193 : ℕ)^8325*100000000000000^6277 ≤ 42696890419451^6277*1000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526406193 1000000000 42696890419451 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394840027/10000000000 : ℝ)^8325 ≤ (4410939310449/10000000000000 : ℝ)^6277 := by
    have hnat : (5394840027 : ℕ)^8325*10000000000000^6277 ≤ 4410939310449^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394840027 10000000000 4410939310449 10000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-217151139/1000000000 : ℝ), (526406193/1000000000 : ℝ), (5394840027/10000000000 : ℝ)] ![(1319371646113/10000000000000 : ℝ), (42696890419451/100000000000000 : ℝ), (4410939310449/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-217151139/1000000000 : ℝ)|^8325 ≤ (1319371646113/10000000000000 : ℝ)^6277
        have hw : |(-217151139/1000000000 : ℝ)|=(217151139/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526406193/1000000000 : ℝ)|^8325 ≤ (42696890419451/100000000000000 : ℝ)^6277
        have hw : |(526406193/1000000000 : ℝ)|=(526406193/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394840027/10000000000 : ℝ)|^8325 ≤ (4410939310449/10000000000000 : ℝ)^6277
        have hw : |(5394840027/10000000000 : ℝ)|=(5394840027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s5_5 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656003581/5000000000 : ℝ)*x 0 + (-131693589/625000000 : ℝ)*x 1 + (5394840021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656003581/5000000000 : ℝ)^8325 ≤ (5401677663199/12500000000000 : ℝ)^6277 := by
    have hnat : (2656003581 : ℕ)^8325*12500000000000^6277 ≤ 5401677663199^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656003581 5000000000 5401677663199 12500000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131693589/625000000 : ℝ)^8325 ≤ (12677185639823/100000000000000 : ℝ)^6277 := by
    have hnat : (131693589 : ℕ)^8325*100000000000000^6277 ≤ 12677185639823^6277*625000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131693589 625000000 12677185639823 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394840021/10000000000 : ℝ)^8325 ≤ (44109393039427/100000000000000 : ℝ)^6277 := by
    have hnat : (5394840021 : ℕ)^8325*100000000000000^6277 ≤ 44109393039427^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394840021 10000000000 44109393039427 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656003581/5000000000 : ℝ), (-131693589/625000000 : ℝ), (5394840021/10000000000 : ℝ)] ![(5401677663199/12500000000000 : ℝ), (12677185639823/100000000000000 : ℝ), (44109393039427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656003581/5000000000 : ℝ)|^8325 ≤ (5401677663199/12500000000000 : ℝ)^6277
        have hw : |(2656003581/5000000000 : ℝ)|=(2656003581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-131693589/625000000 : ℝ)|^8325 ≤ (12677185639823/100000000000000 : ℝ)^6277
        have hw : |(-131693589/625000000 : ℝ)|=(131693589/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394840021/10000000000 : ℝ)|^8325 ≤ (44109393039427/100000000000000 : ℝ)^6277
        have hw : |(5394840021/10000000000 : ℝ)|=(5394840021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s5_6 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312007157/10000000000 : ℝ)*x 0 + (5394840021/10000000000 : ℝ)*x 1 + (-2107097431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312007157/10000000000 : ℝ)^8325 ≤ (8642684250329/20000000000000 : ℝ)^6277 := by
    have hnat : (5312007157 : ℕ)^8325*20000000000000^6277 ≤ 8642684250329^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312007157 10000000000 8642684250329 20000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394840021/10000000000 : ℝ)^8325 ≤ (44109393039427/100000000000000 : ℝ)^6277 := by
    have hnat : (5394840021 : ℕ)^8325*100000000000000^6277 ≤ 44109393039427^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394840021 10000000000 44109393039427 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2107097431/10000000000 : ℝ)^8325 ≤ (12677185695679/100000000000000 : ℝ)^6277 := by
    have hnat : (2107097431 : ℕ)^8325*100000000000000^6277 ≤ 12677185695679^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107097431 10000000000 12677185695679 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312007157/10000000000 : ℝ), (5394840021/10000000000 : ℝ), (-2107097431/10000000000 : ℝ)] ![(8642684250329/20000000000000 : ℝ), (44109393039427/100000000000000 : ℝ), (12677185695679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312007157/10000000000 : ℝ)|^8325 ≤ (8642684250329/20000000000000 : ℝ)^6277
        have hw : |(5312007157/10000000000 : ℝ)|=(5312007157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394840021/10000000000 : ℝ)|^8325 ≤ (44109393039427/100000000000000 : ℝ)^6277
        have hw : |(5394840021/10000000000 : ℝ)|=(5394840021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2107097431/10000000000 : ℝ)|^8325 ≤ (12677185695679/100000000000000 : ℝ)^6277
        have hw : |(-2107097431/10000000000 : ℝ)|=(2107097431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s5_7 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4365995867/10000000000 : ℝ)*x 0 + (4497766703/10000000000 : ℝ)*x 1 + (847619459/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4365995867/10000000000 : ℝ)^8325 ≤ (8329005133713/25000000000000 : ℝ)^6277 := by
    have hnat : (4365995867 : ℕ)^8325*25000000000000^6277 ≤ 8329005133713^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365995867 10000000000 8329005133713 25000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4497766703/10000000000 : ℝ)^8325 ≤ (6931225844673/20000000000000 : ℝ)^6277 := by
    have hnat : (4497766703 : ℕ)^8325*20000000000000^6277 ≤ 6931225844673^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497766703 10000000000 6931225844673 20000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (847619459/2000000000 : ℝ)^8325 ≤ (16013925115053/50000000000000 : ℝ)^6277 := by
    have hnat : (847619459 : ℕ)^8325*50000000000000^6277 ≤ 16013925115053^6277*2000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847619459 2000000000 16013925115053 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4365995867/10000000000 : ℝ), (4497766703/10000000000 : ℝ), (847619459/2000000000 : ℝ)] ![(8329005133713/25000000000000 : ℝ), (6931225844673/20000000000000 : ℝ), (16013925115053/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4365995867/10000000000 : ℝ)|^8325 ≤ (8329005133713/25000000000000 : ℝ)^6277
        have hw : |(4365995867/10000000000 : ℝ)|=(4365995867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4497766703/10000000000 : ℝ)|^8325 ≤ (6931225844673/20000000000000 : ℝ)^6277
        have hw : |(4497766703/10000000000 : ℝ)|=(4497766703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(847619459/2000000000 : ℝ)|^8325 ≤ (16013925115053/50000000000000 : ℝ)^6277
        have hw : |(847619459/2000000000 : ℝ)|=(847619459/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1132_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149278633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2789/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (113/1000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2817/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2789/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2789/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2789/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2789/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2789/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2789/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2789/25000 : ℝ) ^ (2081/512 : ℝ) ≤ (13447543847336549/100000000000000000000 : ℝ) := by
    have hpowers : (2789/25000 : ℝ)^2081 ≤ (13447543847336549/100000000000000000000 : ℝ)^512 := by
      have hnat : (2789 : ℕ)^2081*100000000000000000000^512 ≤ 13447543847336549^512*25000^2081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2789 25000 13447543847336549 100000000000000000000 2081 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2789/25000 : ℝ)) (X := (13447543847336549/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3559/25000 : ℝ) ^ (2081/512 : ℝ) ≤ (36223059307308841/100000000000000000000 : ℝ) := by
    have hpowers : (3559/25000 : ℝ)^2081 ≤ (36223059307308841/100000000000000000000 : ℝ)^512 := by
      have hnat : (3559 : ℕ)^2081*100000000000000000000^512 ≤ 36223059307308841^512*25000^2081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3559 25000 36223059307308841 100000000000000000000 2081 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3559/25000 : ℝ)) (X := (36223059307308841/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013447543847336549/50000000000000000000 : ℝ) ≤ (250016541192881/250000000000000 : ℝ) ^ (2081/512 : ℝ) := by
    have hpowers : (50013447543847336549/50000000000000000000 : ℝ)^512 ≤ (250016541192881/250000000000000 : ℝ)^2081 := by
      have hnat : (50013447543847336549 : ℕ)^512*250000000000000^2081 ≤ 250016541192881^2081*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013447543847336549 50000000000000000000 250016541192881 250000000000000 512 2081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250016541192881/250000000000000 : ℝ)) (X := (50013447543847336549/50000000000000000000 : ℝ)) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004967060315464539/10000000000000000000 : ℝ) ≤ (2500305461174847/2500000000000000 : ℝ) ^ (2081/512 : ℝ) := by
    have hpowers : (10004967060315464539/10000000000000000000 : ℝ)^512 ≤ (2500305461174847/2500000000000000 : ℝ)^2081 := by
      have hnat : (10004967060315464539 : ℕ)^512*2500000000000000^2081 ≤ 2500305461174847^2081*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004967060315464539 10000000000000000000 2500305461174847 2500000000000000 512 2081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500305461174847/2500000000000000 : ℝ)) (X := (10004967060315464539/10000000000000000000 : ℝ)) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036223059307308841/50000000000000000000 : ℝ) ≤ (625111377605221/625000000000000 : ℝ) ^ (2081/512 : ℝ) := by
    have hpowers : (50036223059307308841/50000000000000000000 : ℝ)^512 ≤ (625111377605221/625000000000000 : ℝ)^2081 := by
      have hnat : (50036223059307308841 : ℕ)^512*625000000000000^2081 ≤ 625111377605221^2081*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036223059307308841 50000000000000000000 625111377605221 625000000000000 512 2081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625111377605221/625000000000000 : ℝ)) (X := (50036223059307308841/50000000000000000000 : ℝ)) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13447543847336549/100000000000000000000 : ℝ) ≤ ((962173086245394657/962500000000000000 : ℝ)+2*(140049246037/77000000000000 : ℝ)*(2789/25000 : ℝ))^(2081/512 : ℝ) := by
    rw [show (962173086245394657/962500000000000000 : ℝ)+2*(140049246037/77000000000000 : ℝ)*(2789/25000 : ℝ)=(250016541192881/250000000000000 : ℝ) by norm_num, show 1+2*(13447543847336549/100000000000000000000 : ℝ)=(50013447543847336549/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36223059307308841/100000000000000000000 : ℝ)+(13447543847336549/100000000000000000000 : ℝ) ≤ ((962173086245394657/962500000000000000 : ℝ)+(140049246037/77000000000000 : ℝ)*((3559/25000 : ℝ)+(2789/25000 : ℝ)))^(2081/512 : ℝ) := by
    rw [show (962173086245394657/962500000000000000 : ℝ)+(140049246037/77000000000000 : ℝ)*((3559/25000 : ℝ)+(2789/25000 : ℝ))=(2500305461174847/2500000000000000 : ℝ) by norm_num, show 1+(36223059307308841/100000000000000000000 : ℝ)+(13447543847336549/100000000000000000000 : ℝ)=(10004967060315464539/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36223059307308841/100000000000000000000 : ℝ) ≤ ((962173086245394657/962500000000000000 : ℝ)+2*(140049246037/77000000000000 : ℝ)*(3559/25000 : ℝ))^(2081/512 : ℝ) := by
    rw [show (962173086245394657/962500000000000000 : ℝ)+2*(140049246037/77000000000000 : ℝ)*(3559/25000 : ℝ)=(625111377605221/625000000000000 : ℝ) by norm_num, show 1+2*(36223059307308841/100000000000000000000 : ℝ)=(50036223059307308841/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (962173086245394657/962500000000000000 : ℝ)*(X 1 0+X 2 0)+(140049246037/77000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2081/512 : ℝ)) (lo := (2789/25000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (962173086245394657/962500000000000000 : ℝ)) (alpha := (140049246037/77000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (962173086245394657/962500000000000000 : ℝ)*(X 0 1+X 2 1)+(140049246037/77000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2081/512 : ℝ)) (lo := (2789/25000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (962173086245394657/962500000000000000 : ℝ)) (alpha := (140049246037/77000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (962173086245394657/962500000000000000 : ℝ)*(X 0 2+X 1 2)+(140049246037/77000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2081/512 : ℝ)) (lo := (2789/25000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (962173086245394657/962500000000000000 : ℝ)) (alpha := (140049246037/77000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2171505883/10000000000 : ℝ)*X 0 0+(1348795323/2500000000 : ℝ)*X 0 1+(131593051/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((83520119/156250000 : ℝ)*X 1 0+(-1119107783/5000000000 : ℝ)*X 1 1+(1052744409/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672643933/5000000000 : ℝ)*X 2 0+(2631860917/5000000000 : ℝ)*X 2 1+(-279776939/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((545748161/1250000000 : ℝ)*X 0 0+(4237419617/10000000000 : ℝ)*X 0 1+(2249220901/5000000000 : ℝ)*X 0 2+(545748161/1250000000 : ℝ)*X 1 0+(4237419617/10000000000 : ℝ)*X 1 1+(2249220901/5000000000 : ℝ)*X 1 2+(545748161/1250000000 : ℝ)*X 2 0+(4237419617/10000000000 : ℝ)*X 2 1+(2249220901/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-217151139/1000000000 : ℝ)*X 0 0+(526406193/1000000000 : ℝ)*X 0 1+(5394840027/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656003581/5000000000 : ℝ)*X 1 0+(-131693589/625000000 : ℝ)*X 1 1+(5394840021/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312007157/10000000000 : ℝ)*X 2 0+(5394840021/10000000000 : ℝ)*X 2 1+(-2107097431/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4365995867/10000000000 : ℝ)*X 0 0+(4497766703/10000000000 : ℝ)*X 0 1+(847619459/2000000000 : ℝ)*X 0 2+(4365995867/10000000000 : ℝ)*X 1 0+(4497766703/10000000000 : ℝ)*X 1 1+(847619459/2000000000 : ℝ)*X 1 2+(4365995867/10000000000 : ℝ)*X 2 0+(4497766703/10000000000 : ℝ)*X 2 1+(847619459/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (101155995080322358118935701/9625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1762928497/100000000000000 : ℝ)*(base19) + (865660301/50000000000000 : ℝ)*(base23) + (207070487/100000000000000 : ℝ)*(lower2) + (120548293/50000000000000 : ℝ)*(upper3) + (206147/200000000000 : ℝ)*(upper5) + (1143814908149369/20000000000000 : ℝ)*(major0) + (1143814908149369/20000000000000 : ℝ)*(major1) + (1143814908149369/20000000000000 : ℝ)*(major2) + (3803481198660809/50000000000000 : ℝ)*(sp0) + (1901751554419521/25000000000000 : ℝ)*(sp1) + (7607006249285979/100000000000000 : ℝ)*(sp2) + (3831112998975459/100000000000000 : ℝ)*(sp3) + (45583284963/100000000000000 : ℝ)*(sp4) + (3468948481/12500000000000 : ℝ)*(sp7) + (3831140750563307/100000000000000 : ℝ)*(f.failure) + (7607007980606581/100000000000000 : ℝ)*(f.sum) + (1729639090227/770000000000000000000000000 : ℝ)*base66 + (273874808353433933/19250000000000000000000000000000 : ℝ)*base67 + (19032221562066067/19250000000000000000000000000000 : ℝ)*base70 + (33011497507316067/19250000000000000000000000000000 : ℝ)*base72 + (2448392722343/770000000000000000000000000 : ℝ)*base73 + (148645152552183933/19250000000000000000000000000000 : ℝ)*base75 + (312856658395183933/19250000000000000000000000000000 : ℝ)*base77 + (424759456883433933/19250000000000000000000000000000 : ℝ)*base79 + (926789262447/770000000000000000000000000 : ℝ)*base82 + (51080669/10000000000000000000000 : ℝ)*base90 + (51080669/10000000000000000000000 : ℝ)*base92 + (51080669/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28483751891692063520028231/3437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1584349411/100000000000000 : ℝ)*(base19) + (338841027/20000000000000 : ℝ)*(base23) + (167616503/100000000000000 : ℝ)*(upper3) + (54728853/100000000000000 : ℝ)*(lower4) + (171798251/100000000000000 : ℝ)*(upper5) + (2874397308949191/50000000000000 : ℝ)*(major0) + (2874397308949191/50000000000000 : ℝ)*(major1) + (2874397308949191/50000000000000 : ℝ)*(major2) + (42512387933/100000000000000 : ℝ)*(sp1) + (44750552383/100000000000000 : ℝ)*(sp2) + (3823269539498493/50000000000000 : ℝ)*(sp4) + (7646494982259641/100000000000000 : ℝ)*(sp5) + (1911623158559867/25000000000000 : ℝ)*(sp6) + (1925524940296841/50000000000000 : ℝ)*(sp7) + (1925524940296841/50000000000000 : ℝ)*(f.failure) + (3823269539498493/50000000000000 : ℝ)*(f.sum) + (7283280729617/1925000000000000000000000000 : ℝ)*base65 + (894038290955459987/48125000000000000000000000000000 : ℝ)*base67 + (10543400504209987/48125000000000000000000000000000 : ℝ)*base69 + (498533304251709987/48125000000000000000000000000000 : ℝ)*base71 + (7655385481867/1925000000000000000000000000 : ℝ)*base73 + (1467825340849209987/48125000000000000000000000000000 : ℝ)*base75 + (684927657396709987/48125000000000000000000000000000 : ℝ)*base77 + (786496420461709987/48125000000000000000000000000000 : ℝ)*base79 + (2328568213017/1925000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (61301647/5000000000000000000000 : ℝ)*base90 + (61301647/5000000000000000000000 : ℝ)*base92 + (61301647/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1132_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149278633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2789/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (113/1000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2817/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1132_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1132_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149278633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4133/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (361/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (113/1000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2817/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1132_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1132_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1132_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149278633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4133/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (361/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (113/1000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2817/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1132_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

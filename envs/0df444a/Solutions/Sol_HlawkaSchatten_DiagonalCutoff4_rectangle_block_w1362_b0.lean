-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1362_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:18:37.869697+00:00
-- url     : https://prove2.me/submissions/ee11339a-0fe7-419b-a62b-9a9890bec175

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
theorem support_rectangle_w1362_s0_0 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1797381669/10000000000 : ℝ)*x 0 + (2994161733/5000000000 : ℝ)*x 1 + (4815658383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1797381669/10000000000 : ℝ)^2161 ≤ (10549033655631/100000000000000 : ℝ)^1649 := by
    have hnat : (1797381669 : ℕ)^2161*100000000000000^1649 ≤ 10549033655631^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1797381669 10000000000 10549033655631 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2994161733/5000000000 : ℝ)^2161 ≤ (25534684385411/50000000000000 : ℝ)^1649 := by
    have hnat : (2994161733 : ℕ)^2161*50000000000000^1649 ≤ 25534684385411^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2994161733 5000000000 25534684385411 50000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4815658383/10000000000 : ℝ)^2161 ≤ (38381597550663/100000000000000 : ℝ)^1649 := by
    have hnat : (4815658383 : ℕ)^2161*100000000000000^1649 ≤ 38381597550663^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4815658383 10000000000 38381597550663 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1797381669/10000000000 : ℝ), (2994161733/5000000000 : ℝ), (4815658383/10000000000 : ℝ)] ![(10549033655631/100000000000000 : ℝ), (25534684385411/50000000000000 : ℝ), (38381597550663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1797381669/10000000000 : ℝ)|^2161 ≤ (10549033655631/100000000000000 : ℝ)^1649
        have hw : |(-1797381669/10000000000 : ℝ)|=(1797381669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2994161733/5000000000 : ℝ)|^2161 ≤ (25534684385411/50000000000000 : ℝ)^1649
        have hw : |(2994161733/5000000000 : ℝ)|=(2994161733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4815658383/10000000000 : ℝ)|^2161 ≤ (38381597550663/100000000000000 : ℝ)^1649
        have hw : |(4815658383/10000000000 : ℝ)|=(4815658383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s0_1 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (549957419/1000000000 : ℝ)*x 0 + (-2462956141/10000000000 : ℝ)*x 1 + (4815658897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (549957419/1000000000 : ℝ)^2161 ≤ (11419406471183/25000000000000 : ℝ)^1649 := by
    have hnat : (549957419 : ℕ)^2161*25000000000000^1649 ≤ 11419406471183^1649*1000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549957419 1000000000 11419406471183 25000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2462956141/10000000000 : ℝ)^2161 ≤ (7970385591227/50000000000000 : ℝ)^1649 := by
    have hnat : (2462956141 : ℕ)^2161*50000000000000^1649 ≤ 7970385591227^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2462956141 10000000000 7970385591227 50000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4815658897/10000000000 : ℝ)^2161 ≤ (38381602919307/100000000000000 : ℝ)^1649 := by
    have hnat : (4815658897 : ℕ)^2161*100000000000000^1649 ≤ 38381602919307^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4815658897 10000000000 38381602919307 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(549957419/1000000000 : ℝ), (-2462956141/10000000000 : ℝ), (4815658897/10000000000 : ℝ)] ![(11419406471183/25000000000000 : ℝ), (7970385591227/50000000000000 : ℝ), (38381602919307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(549957419/1000000000 : ℝ)|^2161 ≤ (11419406471183/25000000000000 : ℝ)^1649
        have hw : |(549957419/1000000000 : ℝ)|=(549957419/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2462956141/10000000000 : ℝ)|^2161 ≤ (7970385591227/50000000000000 : ℝ)^1649
        have hw : |(-2462956141/10000000000 : ℝ)|=(2462956141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4815658897/10000000000 : ℝ)|^2161 ≤ (38381602919307/100000000000000 : ℝ)^1649
        have hw : |(4815658897/10000000000 : ℝ)|=(4815658897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s0_2 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2749787031/5000000000 : ℝ)*x 0 + (481565837/1000000000 : ℝ)*x 1 + (-1231478477/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2749787031/5000000000 : ℝ)^2161 ≤ (11419406122879/25000000000000 : ℝ)^1649 := by
    have hnat : (2749787031 : ℕ)^2161*25000000000000^1649 ≤ 11419406122879^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2749787031 5000000000 11419406122879 25000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (481565837/1000000000 : ℝ)^2161 ≤ (239884983843/625000000000 : ℝ)^1649 := by
    have hnat : (481565837 : ℕ)^2161*625000000000^1649 ≤ 239884983843^1649*1000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481565837 1000000000 239884983843 625000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1231478477/5000000000 : ℝ)^2161 ≤ (7970389039069/50000000000000 : ℝ)^1649 := by
    have hnat : (1231478477 : ℕ)^2161*50000000000000^1649 ≤ 7970389039069^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1231478477 5000000000 7970389039069 50000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2749787031/5000000000 : ℝ), (481565837/1000000000 : ℝ), (-1231478477/5000000000 : ℝ)] ![(11419406122879/25000000000000 : ℝ), (239884983843/625000000000 : ℝ), (7970389039069/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2749787031/5000000000 : ℝ)|^2161 ≤ (11419406122879/25000000000000 : ℝ)^1649
        have hw : |(2749787031/5000000000 : ℝ)|=(2749787031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(481565837/1000000000 : ℝ)|^2161 ≤ (239884983843/625000000000 : ℝ)^1649
        have hw : |(481565837/1000000000 : ℝ)|=(481565837/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1231478477/5000000000 : ℝ)|^2161 ≤ (7970389039069/50000000000000 : ℝ)^1649
        have hw : |(-1231478477/5000000000 : ℝ)|=(1231478477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s0_3 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4175768159/10000000000 : ℝ)*x 0 + (1552816697/5000000000 : ℝ)*x 1 + (1395090011/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4175768159/10000000000 : ℝ)^2161 ≤ (3184038855043/10000000000000 : ℝ)^1649 := by
    have hnat : (4175768159 : ℕ)^2161*10000000000000^1649 ≤ 3184038855043^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4175768159 10000000000 3184038855043 10000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1552816697/5000000000 : ℝ)^2161 ≤ (2160067322193/10000000000000 : ℝ)^1649 := by
    have hnat : (1552816697 : ℕ)^2161*10000000000000^1649 ≤ 2160067322193^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1552816697 5000000000 2160067322193 10000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1395090011/2500000000 : ℝ)^2161 ≤ (46558938211783/100000000000000 : ℝ)^1649 := by
    have hnat : (1395090011 : ℕ)^2161*100000000000000^1649 ≤ 46558938211783^1649*2500000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1395090011 2500000000 46558938211783 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4175768159/10000000000 : ℝ), (1552816697/5000000000 : ℝ), (1395090011/2500000000 : ℝ)] ![(3184038855043/10000000000000 : ℝ), (2160067322193/10000000000000 : ℝ), (46558938211783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4175768159/10000000000 : ℝ)|^2161 ≤ (3184038855043/10000000000000 : ℝ)^1649
        have hw : |(4175768159/10000000000 : ℝ)|=(4175768159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1552816697/5000000000 : ℝ)|^2161 ≤ (2160067322193/10000000000000 : ℝ)^1649
        have hw : |(1552816697/5000000000 : ℝ)|=(1552816697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1395090011/2500000000 : ℝ)|^2161 ≤ (46558938211783/100000000000000 : ℝ)^1649
        have hw : |(1395090011/2500000000 : ℝ)|=(1395090011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s0_4 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-360346887/2000000000 : ℝ)*x 0 + (4845802911/10000000000 : ℝ)*x 1 + (37231887/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (360346887/2000000000 : ℝ)^2161 ≤ (5291262591681/50000000000000 : ℝ)^1649 := by
    have hnat : (360346887 : ℕ)^2161*50000000000000^1649 ≤ 5291262591681^1649*2000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      360346887 2000000000 5291262591681 50000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4845802911/10000000000 : ℝ)^2161 ≤ (3869675763533/10000000000000 : ℝ)^1649 := by
    have hnat : (4845802911 : ℕ)^2161*10000000000000^1649 ≤ 3869675763533^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4845802911 10000000000 3869675763533 10000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (37231887/62500000 : ℝ)^2161 ≤ (50720717167153/100000000000000 : ℝ)^1649 := by
    have hnat : (37231887 : ℕ)^2161*100000000000000^1649 ≤ 50720717167153^1649*62500000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37231887 62500000 50720717167153 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-360346887/2000000000 : ℝ), (4845802911/10000000000 : ℝ), (37231887/62500000 : ℝ)] ![(5291262591681/50000000000000 : ℝ), (3869675763533/10000000000000 : ℝ), (50720717167153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-360346887/2000000000 : ℝ)|^2161 ≤ (5291262591681/50000000000000 : ℝ)^1649
        have hw : |(-360346887/2000000000 : ℝ)|=(360346887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4845802911/10000000000 : ℝ)|^2161 ≤ (3869675763533/10000000000000 : ℝ)^1649
        have hw : |(4845802911/10000000000 : ℝ)|=(4845802911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(37231887/62500000 : ℝ)|^2161 ≤ (50720717167153/100000000000000 : ℝ)^1649
        have hw : |(37231887/62500000 : ℝ)|=(37231887/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s0_5 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2589931127/5000000000 : ℝ)*x 0 + (-660757527/5000000000 : ℝ)*x 1 + (1489275291/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2589931127/5000000000 : ℝ)^2161 ≤ (21114778589483/50000000000000 : ℝ)^1649 := by
    have hnat : (2589931127 : ℕ)^2161*50000000000000^1649 ≤ 21114778589483^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589931127 5000000000 21114778589483 50000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (660757527/5000000000 : ℝ)^2161 ≤ (7049734072043/100000000000000 : ℝ)^1649 := by
    have hnat : (660757527 : ℕ)^2161*100000000000000^1649 ≤ 7049734072043^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660757527 5000000000 7049734072043 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1489275291/2500000000 : ℝ)^2161 ≤ (25360354365871/50000000000000 : ℝ)^1649 := by
    have hnat : (1489275291 : ℕ)^2161*50000000000000^1649 ≤ 25360354365871^1649*2500000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1489275291 2500000000 25360354365871 50000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2589931127/5000000000 : ℝ), (-660757527/5000000000 : ℝ), (1489275291/2500000000 : ℝ)] ![(21114778589483/50000000000000 : ℝ), (7049734072043/100000000000000 : ℝ), (25360354365871/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2589931127/5000000000 : ℝ)|^2161 ≤ (21114778589483/50000000000000 : ℝ)^1649
        have hw : |(2589931127/5000000000 : ℝ)|=(2589931127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-660757527/5000000000 : ℝ)|^2161 ≤ (7049734072043/100000000000000 : ℝ)^1649
        have hw : |(-660757527/5000000000 : ℝ)|=(660757527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1489275291/2500000000 : ℝ)|^2161 ≤ (25360354365871/50000000000000 : ℝ)^1649
        have hw : |(1489275291/2500000000 : ℝ)|=(1489275291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s0_6 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (129496549/250000000 : ℝ)*x 0 + (2978551109/5000000000 : ℝ)*x 1 + (-1321513823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129496549/250000000 : ℝ)^2161 ≤ (42229554037881/100000000000000 : ℝ)^1649 := by
    have hnat : (129496549 : ℕ)^2161*100000000000000^1649 ≤ 42229554037881^1649*250000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129496549 250000000 42229554037881 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2978551109/5000000000 : ℝ)^2161 ≤ (50720720492223/100000000000000 : ℝ)^1649 := by
    have hnat : (2978551109 : ℕ)^2161*100000000000000^1649 ≤ 50720720492223^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2978551109 5000000000 50720720492223 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1321513823/10000000000 : ℝ)^2161 ≤ (3524862733107/50000000000000 : ℝ)^1649 := by
    have hnat : (1321513823 : ℕ)^2161*50000000000000^1649 ≤ 3524862733107^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321513823 10000000000 3524862733107 50000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(129496549/250000000 : ℝ), (2978551109/5000000000 : ℝ), (-1321513823/10000000000 : ℝ)] ![(42229554037881/100000000000000 : ℝ), (50720720492223/100000000000000 : ℝ), (3524862733107/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(129496549/250000000 : ℝ)|^2161 ≤ (42229554037881/100000000000000 : ℝ)^1649
        have hw : |(129496549/250000000 : ℝ)|=(129496549/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2978551109/5000000000 : ℝ)|^2161 ≤ (50720720492223/100000000000000 : ℝ)^1649
        have hw : |(2978551109/5000000000 : ℝ)|=(2978551109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1321513823/10000000000 : ℝ)|^2161 ≤ (3524862733107/50000000000000 : ℝ)^1649
        have hw : |(-1321513823/10000000000 : ℝ)|=(1321513823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s0_7 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (523118671/1250000000 : ℝ)*x 0 + (1103349309/2000000000 : ℝ)*x 1 + (158576093/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (523118671/1250000000 : ℝ)^2161 ≤ (31932163489719/100000000000000 : ℝ)^1649 := by
    have hnat : (523118671 : ℕ)^2161*100000000000000^1649 ≤ 31932163489719^1649*1250000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523118671 1250000000 31932163489719 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1103349309/2000000000 : ℝ)^2161 ≤ (22932314480479/50000000000000 : ℝ)^1649 := by
    have hnat : (1103349309 : ℕ)^2161*50000000000000^1649 ≤ 22932314480479^1649*2000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103349309 2000000000 22932314480479 50000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (158576093/500000000 : ℝ)^2161 ≤ (693850235433/3125000000000 : ℝ)^1649 := by
    have hnat : (158576093 : ℕ)^2161*3125000000000^1649 ≤ 693850235433^1649*500000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158576093 500000000 693850235433 3125000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(523118671/1250000000 : ℝ), (1103349309/2000000000 : ℝ), (158576093/500000000 : ℝ)] ![(31932163489719/100000000000000 : ℝ), (22932314480479/50000000000000 : ℝ), (693850235433/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(523118671/1250000000 : ℝ)|^2161 ≤ (31932163489719/100000000000000 : ℝ)^1649
        have hw : |(523118671/1250000000 : ℝ)|=(523118671/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1103349309/2000000000 : ℝ)|^2161 ≤ (22932314480479/50000000000000 : ℝ)^1649
        have hw : |(1103349309/2000000000 : ℝ)|=(1103349309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(158576093/500000000 : ℝ)|^2161 ≤ (693850235433/3125000000000 : ℝ)^1649
        have hw : |(158576093/500000000 : ℝ)|=(158576093/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1362_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155517229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1563/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3341/12500 : ℝ)*pair X 0 0 := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
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
  have hpowlo : (0 : ℝ) ^ (4321/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4321 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4321*1^1024 ≤ 0^1024*1^4321 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4321 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4321/1024 : ℝ) ≤ (523289455721250473/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4321 ≤ (523289455721250473/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4321*25000000000000000000^1024 ≤ 523289455721250473^1024*5^4321 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 523289455721250473 25000000000000000000 4321 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (523289455721250473/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4321/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4321 := by
      have hnat : (1 : ℕ)^1024*1^4321 ≤ 1^4321*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25523289455721250473/25000000000000000000 : ℝ) ≤ (2512303198971817/2500000000000000 : ℝ) ^ (4321/1024 : ℝ) := by
    have hpowers : (25523289455721250473/25000000000000000000 : ℝ)^1024 ≤ (2512303198971817/2500000000000000 : ℝ)^4321 := by
      have hnat : (25523289455721250473 : ℕ)^1024*2500000000000000^4321 ≤ 2512303198971817^4321*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25523289455721250473 25000000000000000000 2512303198971817 2500000000000000 1024 4321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2512303198971817/2500000000000000 : ℝ)) (X := (25523289455721250473/25000000000000000000 : ℝ)) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (13023289455721250473/12500000000000000000 : ℝ) ≤ (1262303198971817/1250000000000000 : ℝ) ^ (4321/1024 : ℝ) := by
    have hpowers : (13023289455721250473/12500000000000000000 : ℝ)^1024 ≤ (1262303198971817/1250000000000000 : ℝ)^4321 := by
      have hnat : (13023289455721250473 : ℕ)^1024*1250000000000000^4321 ≤ 1262303198971817^4321*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13023289455721250473 12500000000000000000 1262303198971817 1250000000000000 1024 4321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1262303198971817/1250000000000000 : ℝ)) (X := (13023289455721250473/12500000000000000000 : ℝ)) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(12303198971817/1000000000000000 : ℝ)*(0 : ℝ))^(4321/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(12303198971817/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(523289455721250473/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(12303198971817/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4321/1024 : ℝ) := by
    rw [show (1 : ℝ)+(12303198971817/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2512303198971817/2500000000000000 : ℝ) by norm_num, show 1+(523289455721250473/25000000000000000000 : ℝ)+(0 : ℝ)=(25523289455721250473/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(523289455721250473/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(12303198971817/1000000000000000 : ℝ)*(2/5 : ℝ))^(4321/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(12303198971817/1000000000000000 : ℝ)*(2/5 : ℝ)=(1262303198971817/1250000000000000 : ℝ) by norm_num, show 1+2*(523289455721250473/25000000000000000000 : ℝ)=(13023289455721250473/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(12303198971817/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4321/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12303198971817/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(12303198971817/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4321/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12303198971817/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(12303198971817/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4321/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12303198971817/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1797381669/10000000000 : ℝ)*X 0 0+(2994161733/5000000000 : ℝ)*X 0 1+(4815658383/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((549957419/1000000000 : ℝ)*X 1 0+(-2462956141/10000000000 : ℝ)*X 1 1+(4815658897/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2749787031/5000000000 : ℝ)*X 2 0+(481565837/1000000000 : ℝ)*X 2 1+(-1231478477/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4175768159/10000000000 : ℝ)*X 0 0+(1552816697/5000000000 : ℝ)*X 0 1+(1395090011/2500000000 : ℝ)*X 0 2+(4175768159/10000000000 : ℝ)*X 1 0+(1552816697/5000000000 : ℝ)*X 1 1+(1395090011/2500000000 : ℝ)*X 1 2+(4175768159/10000000000 : ℝ)*X 2 0+(1552816697/5000000000 : ℝ)*X 2 1+(1395090011/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-360346887/2000000000 : ℝ)*X 0 0+(4845802911/10000000000 : ℝ)*X 0 1+(37231887/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2589931127/5000000000 : ℝ)*X 1 0+(-660757527/5000000000 : ℝ)*X 1 1+(1489275291/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((129496549/250000000 : ℝ)*X 2 0+(2978551109/5000000000 : ℝ)*X 2 1+(-1321513823/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((523118671/1250000000 : ℝ)*X 0 0+(1103349309/2000000000 : ℝ)*X 0 1+(158576093/500000000 : ℝ)*X 0 2+(523118671/1250000000 : ℝ)*X 1 0+(1103349309/2000000000 : ℝ)*X 1 1+(158576093/500000000 : ℝ)*X 1 2+(523118671/1250000000 : ℝ)*X 2 0+(1103349309/2000000000 : ℝ)*X 2 1+(158576093/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13592245025202803723907/2000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (89023797/50000000000000 : ℝ)*(base1) + (316022751/20000000000000 : ℝ)*(base19) + (390066503/25000000000000 : ℝ)*(base23) + (270446731/100000000000000 : ℝ)*(upper3) + (2187943/4000000000000 : ℝ)*(upper5) + (25137162905581/4000000000000 : ℝ)*(major0) + (25137162905581/4000000000000 : ℝ)*(major1) + (25137162905581/4000000000000 : ℝ)*(major2) + (852763976784029/100000000000000 : ℝ)*(sp0) + (213191664716679/25000000000000 : ℝ)*(sp1) + (852766678714459/100000000000000 : ℝ)*(sp2) + (404086913684547/100000000000000 : ℝ)*(sp3) + (4440244037/100000000000000 : ℝ)*(sp4) + (517605803/20000000000000 : ℝ)*(sp7) + (404089679761157/100000000000000 : ℝ)*(f.failure) + (852768238980471/100000000000000 : ℝ)*(f.sum) + (6871505016677/2000000000000000000000000000 : ℝ)*base65 + (10311276645323/4000000000000000000000000000 : ℝ)*base68 + (8585754550677/4000000000000000000000000000 : ℝ)*base69 + (23045404878677/4000000000000000000000000000 : ℝ)*base71 + (2075074463323/2000000000000000000000000000 : ℝ)*base74 + (8077930130677/4000000000000000000000000000 : ℝ)*base75 + (22016995206677/4000000000000000000000000000 : ℝ)*base77 + (8874100918677/4000000000000000000000000000 : ℝ)*base79 + (5168630846677/2000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (18473953/10000000000000000000000 : ℝ)*base89 + (18473953/10000000000000000000000 : ℝ)*base91 + (18473953/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (365076171982067224236267/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (888744993/100000000000000 : ℝ)*(base19) + (638118827/50000000000000 : ℝ)*(base23) + (439846383/100000000000000 : ℝ)*(base39) + (1769791/4000000000000 : ℝ)*(upper3) + (274597691/100000000000000 : ℝ)*(upper5) + (331560976829207/50000000000000 : ℝ)*(major0) + (331560976829207/50000000000000 : ℝ)*(major1) + (663121513812031/100000000000000 : ℝ)*(major2) + (270532207/12500000000000 : ℝ)*(sp1) + (2312779009/100000000000000 : ℝ)*(sp2) + (179969096316769/20000000000000 : ℝ)*(sp4) + (899842428581197/100000000000000 : ℝ)*(sp5) + (179968466482713/20000000000000 : ℝ)*(sp6) + (426397742502481/100000000000000 : ℝ)*(sp7) + (426397742502481/100000000000000 : ℝ)*(f.failure) + (224961480357557/25000000000000 : ℝ)*(f.sum) + (23898378429713/20000000000000000000000000000 : ℝ)*base65 + (557861689469673/100000000000000000000000000000 : ℝ)*base68 + (75412362459119/50000000000000000000000000000 : ℝ)*base69 + (403768464069673/100000000000000000000000000000 : ℝ)*base72 + (30885493130287/20000000000000000000000000000 : ℝ)*base74 + (141762454540881/50000000000000000000000000000 : ℝ)*base76 + (41456517159119/50000000000000000000000000000 : ℝ)*base77 + (46107816790881/50000000000000000000000000000 : ℝ)*base80 + (9379538484119/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (29254851/10000000000000000000000 : ℝ)*base90 + (29254851/10000000000000000000000 : ℝ)*base92 + (29254851/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1362_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155517229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1563/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3341/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1362_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1362_s1_0 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-989657217/5000000000 : ℝ)*x 0 + (2816640131/5000000000 : ℝ)*x 1 + (1010833651/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (989657217/5000000000 : ℝ)^2161 ≤ (11969853097137/100000000000000 : ℝ)^1649 := by
    have hnat : (989657217 : ℕ)^2161*100000000000000^1649 ≤ 11969853097137^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      989657217 5000000000 11969853097137 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2816640131/5000000000 : ℝ)^2161 ≤ (4713841242239/10000000000000 : ℝ)^1649 := by
    have hnat : (2816640131 : ℕ)^2161*10000000000000^1649 ≤ 4713841242239^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2816640131 5000000000 4713841242239 10000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1010833651/2000000000 : ℝ)^2161 ≤ (40891734465951/100000000000000 : ℝ)^1649 := by
    have hnat : (1010833651 : ℕ)^2161*100000000000000^1649 ≤ 40891734465951^1649*2000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010833651 2000000000 40891734465951 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-989657217/5000000000 : ℝ), (2816640131/5000000000 : ℝ), (1010833651/2000000000 : ℝ)] ![(11969853097137/100000000000000 : ℝ), (4713841242239/10000000000000 : ℝ), (40891734465951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-989657217/5000000000 : ℝ)|^2161 ≤ (11969853097137/100000000000000 : ℝ)^1649
        have hw : |(-989657217/5000000000 : ℝ)|=(989657217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2816640131/5000000000 : ℝ)|^2161 ≤ (4713841242239/10000000000000 : ℝ)^1649
        have hw : |(2816640131/5000000000 : ℝ)|=(2816640131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1010833651/2000000000 : ℝ)|^2161 ≤ (40891734465951/100000000000000 : ℝ)^1649
        have hw : |(1010833651/2000000000 : ℝ)|=(1010833651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s1_1 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5403640189/10000000000 : ℝ)*x 0 + (-2287820407/10000000000 : ℝ)*x 1 + (315885577/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5403640189/10000000000 : ℝ)^2161 ≤ (4463627123557/10000000000000 : ℝ)^1649 := by
    have hnat : (5403640189 : ℕ)^2161*10000000000000^1649 ≤ 4463627123557^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403640189 10000000000 4463627123557 10000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2287820407/10000000000 : ℝ)^2161 ≤ (14471983922049/100000000000000 : ℝ)^1649 := by
    have hnat : (2287820407 : ℕ)^2161*100000000000000^1649 ≤ 14471983922049^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2287820407 10000000000 14471983922049 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (315885577/625000000 : ℝ)^2161 ≤ (5111468103109/12500000000000 : ℝ)^1649 := by
    have hnat : (315885577 : ℕ)^2161*12500000000000^1649 ≤ 5111468103109^1649*625000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315885577 625000000 5111468103109 12500000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5403640189/10000000000 : ℝ), (-2287820407/10000000000 : ℝ), (315885577/625000000 : ℝ)] ![(4463627123557/10000000000000 : ℝ), (14471983922049/100000000000000 : ℝ), (5111468103109/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5403640189/10000000000 : ℝ)|^2161 ≤ (4463627123557/10000000000000 : ℝ)^1649
        have hw : |(5403640189/10000000000 : ℝ)|=(5403640189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2287820407/10000000000 : ℝ)|^2161 ≤ (14471983922049/100000000000000 : ℝ)^1649
        have hw : |(-2287820407/10000000000 : ℝ)|=(2287820407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(315885577/625000000 : ℝ)|^2161 ≤ (5111468103109/12500000000000 : ℝ)^1649
        have hw : |(315885577/625000000 : ℝ)|=(315885577/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s1_2 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2701820203/5000000000 : ℝ)*x 0 + (2527084219/5000000000 : ℝ)*x 1 + (-2287821139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2701820203/5000000000 : ℝ)^2161 ≤ (11159068396159/25000000000000 : ℝ)^1649 := by
    have hnat : (2701820203 : ℕ)^2161*25000000000000^1649 ≤ 11159068396159^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701820203 5000000000 11159068396159 25000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2527084219/5000000000 : ℝ)^2161 ≤ (40891736406261/100000000000000 : ℝ)^1649 := by
    have hnat : (2527084219 : ℕ)^2161*100000000000000^1649 ≤ 40891736406261^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2527084219 5000000000 40891736406261 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2287821139/10000000000 : ℝ)^2161 ≤ (1447198999013/10000000000000 : ℝ)^1649 := by
    have hnat : (2287821139 : ℕ)^2161*10000000000000^1649 ≤ 1447198999013^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2287821139 10000000000 1447198999013 10000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2701820203/5000000000 : ℝ), (2527084219/5000000000 : ℝ), (-2287821139/10000000000 : ℝ)] ![(11159068396159/25000000000000 : ℝ), (40891736406261/100000000000000 : ℝ), (1447198999013/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2701820203/5000000000 : ℝ)|^2161 ≤ (11159068396159/25000000000000 : ℝ)^1649
        have hw : |(2701820203/5000000000 : ℝ)|=(2701820203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2527084219/5000000000 : ℝ)|^2161 ≤ (40891736406261/100000000000000 : ℝ)^1649
        have hw : |(2527084219/5000000000 : ℝ)|=(2527084219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2287821139/10000000000 : ℝ)|^2161 ≤ (1447198999013/10000000000000 : ℝ)^1649
        have hw : |(-2287821139/10000000000 : ℝ)|=(2287821139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s1_3 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (857746693/2000000000 : ℝ)*x 0 + (929416719/2500000000 : ℝ)*x 1 + (2469894239/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (857746693/2000000000 : ℝ)^2161 ≤ (8243477757033/25000000000000 : ℝ)^1649 := by
    have hnat : (857746693 : ℕ)^2161*25000000000000^1649 ≤ 8243477757033^1649*2000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      857746693 2000000000 8243477757033 25000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (929416719/2500000000 : ℝ)^2161 ≤ (27342815510783/100000000000000 : ℝ)^1649 := by
    have hnat : (929416719 : ℕ)^2161*100000000000000^1649 ≤ 27342815510783^1649*2500000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      929416719 2500000000 27342815510783 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2469894239/5000000000 : ℝ)^2161 ≤ (19841636724339/50000000000000 : ℝ)^1649 := by
    have hnat : (2469894239 : ℕ)^2161*50000000000000^1649 ≤ 19841636724339^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2469894239 5000000000 19841636724339 50000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(857746693/2000000000 : ℝ), (929416719/2500000000 : ℝ), (2469894239/5000000000 : ℝ)] ![(8243477757033/25000000000000 : ℝ), (27342815510783/100000000000000 : ℝ), (19841636724339/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(857746693/2000000000 : ℝ)|^2161 ≤ (8243477757033/25000000000000 : ℝ)^1649
        have hw : |(857746693/2000000000 : ℝ)|=(857746693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(929416719/2500000000 : ℝ)|^2161 ≤ (27342815510783/100000000000000 : ℝ)^1649
        have hw : |(929416719/2500000000 : ℝ)|=(929416719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2469894239/5000000000 : ℝ)|^2161 ≤ (19841636724339/50000000000000 : ℝ)^1649
        have hw : |(2469894239/5000000000 : ℝ)|=(2469894239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s1_4 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-989907781/5000000000 : ℝ)*x 0 + (5061324039/10000000000 : ℝ)*x 1 + (2812998159/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (989907781/5000000000 : ℝ)^2161 ≤ (2394764954747/20000000000000 : ℝ)^1649 := by
    have hnat : (989907781 : ℕ)^2161*20000000000000^1649 ≤ 2394764954747^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      989907781 5000000000 2394764954747 20000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5061324039/10000000000 : ℝ)^2161 ≤ (20483811187479/50000000000000 : ℝ)^1649 := by
    have hnat : (5061324039 : ℕ)^2161*50000000000000^1649 ≤ 20483811187479^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5061324039 10000000000 20483811187479 50000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2812998159/5000000000 : ℝ)^2161 ≤ (47058552829891/100000000000000 : ℝ)^1649 := by
    have hnat : (2812998159 : ℕ)^2161*100000000000000^1649 ≤ 47058552829891^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2812998159 5000000000 47058552829891 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-989907781/5000000000 : ℝ), (5061324039/10000000000 : ℝ), (2812998159/5000000000 : ℝ)] ![(2394764954747/20000000000000 : ℝ), (20483811187479/50000000000000 : ℝ), (47058552829891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-989907781/5000000000 : ℝ)|^2161 ≤ (2394764954747/20000000000000 : ℝ)^1649
        have hw : |(-989907781/5000000000 : ℝ)|=(989907781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5061324039/10000000000 : ℝ)|^2161 ≤ (20483811187479/50000000000000 : ℝ)^1649
        have hw : |(5061324039/10000000000 : ℝ)|=(5061324039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2812998159/5000000000 : ℝ)|^2161 ≤ (47058552829891/100000000000000 : ℝ)^1649
        have hw : |(2812998159/5000000000 : ℝ)|=(2812998159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s1_5 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1050624103/2000000000 : ℝ)*x 0 + (-857996567/5000000000 : ℝ)*x 1 + (5625996389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050624103/2000000000 : ℝ)^2161 ≤ (8602791751891/20000000000000 : ℝ)^1649 := by
    have hnat : (1050624103 : ℕ)^2161*20000000000000^1649 ≤ 8602791751891^1649*2000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050624103 2000000000 8602791751891 20000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (857996567/5000000000 : ℝ)^2161 ≤ (9927487613493/100000000000000 : ℝ)^1649 := by
    have hnat : (857996567 : ℕ)^2161*100000000000000^1649 ≤ 9927487613493^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      857996567 5000000000 9927487613493 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5625996389/10000000000 : ℝ)^2161 ≤ (11764638402041/25000000000000 : ℝ)^1649 := by
    have hnat : (5625996389 : ℕ)^2161*25000000000000^1649 ≤ 11764638402041^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5625996389 10000000000 11764638402041 25000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050624103/2000000000 : ℝ), (-857996567/5000000000 : ℝ), (5625996389/10000000000 : ℝ)] ![(8602791751891/20000000000000 : ℝ), (9927487613493/100000000000000 : ℝ), (11764638402041/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050624103/2000000000 : ℝ)|^2161 ≤ (8602791751891/20000000000000 : ℝ)^1649
        have hw : |(1050624103/2000000000 : ℝ)|=(1050624103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-857996567/5000000000 : ℝ)|^2161 ≤ (9927487613493/100000000000000 : ℝ)^1649
        have hw : |(-857996567/5000000000 : ℝ)|=(857996567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5625996389/10000000000 : ℝ)|^2161 ≤ (11764638402041/25000000000000 : ℝ)^1649
        have hw : |(5625996389/10000000000 : ℝ)|=(5625996389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s1_6 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (656640051/1250000000 : ℝ)*x 0 + (5625996477/10000000000 : ℝ)*x 1 + (-857996579/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (656640051/1250000000 : ℝ)^2161 ≤ (1720558304451/4000000000000 : ℝ)^1649 := by
    have hnat : (656640051 : ℕ)^2161*4000000000000^1649 ≤ 1720558304451^1649*1250000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656640051 1250000000 1720558304451 4000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5625996477/10000000000 : ℝ)^2161 ≤ (47058554572783/100000000000000 : ℝ)^1649 := by
    have hnat : (5625996477 : ℕ)^2161*100000000000000^1649 ≤ 47058554572783^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5625996477 10000000000 47058554572783 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (857996579/5000000000 : ℝ)^2161 ≤ (198549755909/2000000000000 : ℝ)^1649 := by
    have hnat : (857996579 : ℕ)^2161*2000000000000^1649 ≤ 198549755909^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      857996579 5000000000 198549755909 2000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(656640051/1250000000 : ℝ), (5625996477/10000000000 : ℝ), (-857996579/5000000000 : ℝ)] ![(1720558304451/4000000000000 : ℝ), (47058554572783/100000000000000 : ℝ), (198549755909/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(656640051/1250000000 : ℝ)|^2161 ≤ (1720558304451/4000000000000 : ℝ)^1649
        have hw : |(656640051/1250000000 : ℝ)|=(656640051/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5625996477/10000000000 : ℝ)|^2161 ≤ (47058554572783/100000000000000 : ℝ)^1649
        have hw : |(5625996477/10000000000 : ℝ)|=(5625996477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-857996579/5000000000 : ℝ)|^2161 ≤ (198549755909/2000000000000 : ℝ)^1649
        have hw : |(-857996579/5000000000 : ℝ)|=(857996579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s1_7 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2144895841/5000000000 : ℝ)*x 0 + (615586109/1250000000 : ℝ)*x 1 + (233314727/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2144895841/5000000000 : ℝ)^2161 ≤ (103076792877/312500000000 : ℝ)^1649 := by
    have hnat : (2144895841 : ℕ)^2161*312500000000^1649 ≤ 103076792877^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144895841 5000000000 103076792877 312500000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (615586109/1250000000 : ℝ)^2161 ≤ (988109622689/2500000000000 : ℝ)^1649 := by
    have hnat : (615586109 : ℕ)^2161*2500000000000^1649 ≤ 988109622689^1649*1250000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      615586109 1250000000 988109622689 2500000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (233314727/625000000 : ℝ)^2161 ≤ (859095042593/3125000000000 : ℝ)^1649 := by
    have hnat : (233314727 : ℕ)^2161*3125000000000^1649 ≤ 859095042593^1649*625000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233314727 625000000 859095042593 3125000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2144895841/5000000000 : ℝ), (615586109/1250000000 : ℝ), (233314727/625000000 : ℝ)] ![(103076792877/312500000000 : ℝ), (988109622689/2500000000000 : ℝ), (859095042593/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2144895841/5000000000 : ℝ)|^2161 ≤ (103076792877/312500000000 : ℝ)^1649
        have hw : |(2144895841/5000000000 : ℝ)|=(2144895841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(615586109/1250000000 : ℝ)|^2161 ≤ (988109622689/2500000000000 : ℝ)^1649
        have hw : |(615586109/1250000000 : ℝ)|=(615586109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(233314727/625000000 : ℝ)|^2161 ≤ (859095042593/3125000000000 : ℝ)^1649
        have hw : |(233314727/625000000 : ℝ)|=(233314727/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1362_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155517229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3341/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1563/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (7073/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19313/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3341/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1563/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3341/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1563/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3341/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1563/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3341/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1563/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3341/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1563/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3341/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1563/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (1563/100000 : ℝ) ^ (4321/1024 : ℝ) ≤ (299164970059/12500000000000000000 : ℝ) := by
    have hpowers : (1563/100000 : ℝ)^4321 ≤ (299164970059/12500000000000000000 : ℝ)^1024 := by
      have hnat : (1563 : ℕ)^4321*12500000000000000000^1024 ≤ 299164970059^1024*100000^4321 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563 100000 299164970059 12500000000000000000 4321 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1563/100000 : ℝ)) (X := (299164970059/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3341/12500 : ℝ) ^ (4321/1024 : ℝ) ≤ (95476209735795429/25000000000000000000 : ℝ) := by
    have hpowers : (3341/12500 : ℝ)^4321 ≤ (95476209735795429/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3341 : ℕ)^4321*25000000000000000000^1024 ≤ 95476209735795429^1024*12500^4321 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3341 12500 95476209735795429 25000000000000000000 4321 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3341/12500 : ℝ)) (X := (95476209735795429/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250000299164970059/6250000000000000000 : ℝ) ≤ (400000004537393/400000000000000 : ℝ) ^ (4321/1024 : ℝ) := by
    have hpowers : (6250000299164970059/6250000000000000000 : ℝ)^1024 ≤ (400000004537393/400000000000000 : ℝ)^4321 := by
      have hnat : (6250000299164970059 : ℕ)^1024*400000000000000^4321 ≤ 400000004537393^4321*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250000299164970059 6250000000000000000 400000004537393 400000000000000 1024 4321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400000004537393/400000000000000 : ℝ)) (X := (6250000299164970059/6250000000000000000 : ℝ)) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25095476808065735547/25000000000000000000 : ℝ) ≤ (10009037363665339/10000000000000000 : ℝ) ^ (4321/1024 : ℝ) := by
    have hpowers : (25095476808065735547/25000000000000000000 : ℝ)^1024 ≤ (10009037363665339/10000000000000000 : ℝ)^4321 := by
      have hnat : (25095476808065735547 : ℕ)^1024*10000000000000000^4321 ≤ 10009037363665339^4321*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25095476808065735547 25000000000000000000 10009037363665339 10000000000000000 1024 4321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10009037363665339/10000000000000000 : ℝ)) (X := (25095476808065735547/25000000000000000000 : ℝ)) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12595476209735795429/12500000000000000000 : ℝ) ≤ (10018074613895853/10000000000000000 : ℝ) ^ (4321/1024 : ℝ) := by
    have hpowers : (12595476209735795429/12500000000000000000 : ℝ)^1024 ≤ (10018074613895853/10000000000000000 : ℝ)^4321 := by
      have hnat : (12595476209735795429 : ℕ)^1024*10000000000000000^4321 ≤ 10018074613895853^4321*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12595476209735795429 12500000000000000000 10018074613895853 10000000000000000 1024 4321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10018074613895853/10000000000000000 : ℝ)) (X := (12595476209735795429/12500000000000000000 : ℝ)) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(299164970059/12500000000000000000 : ℝ) ≤ ((251621752410366784361/251650000000000000000 : ℝ)+2*(4518625115257/1258250000000000 : ℝ)*(1563/100000 : ℝ))^(4321/1024 : ℝ) := by
    rw [show (251621752410366784361/251650000000000000000 : ℝ)+2*(4518625115257/1258250000000000 : ℝ)*(1563/100000 : ℝ)=(400000004537393/400000000000000 : ℝ) by norm_num, show 1+2*(299164970059/12500000000000000000 : ℝ)=(6250000299164970059/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(95476209735795429/25000000000000000000 : ℝ)+(299164970059/12500000000000000000 : ℝ) ≤ ((251621752410366784361/251650000000000000000 : ℝ)+(4518625115257/1258250000000000 : ℝ)*((3341/12500 : ℝ)+(1563/100000 : ℝ)))^(4321/1024 : ℝ) := by
    rw [show (251621752410366784361/251650000000000000000 : ℝ)+(4518625115257/1258250000000000 : ℝ)*((3341/12500 : ℝ)+(1563/100000 : ℝ))=(10009037363665339/10000000000000000 : ℝ) by norm_num, show 1+(95476209735795429/25000000000000000000 : ℝ)+(299164970059/12500000000000000000 : ℝ)=(25095476808065735547/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(95476209735795429/25000000000000000000 : ℝ) ≤ ((251621752410366784361/251650000000000000000 : ℝ)+2*(4518625115257/1258250000000000 : ℝ)*(3341/12500 : ℝ))^(4321/1024 : ℝ) := by
    rw [show (251621752410366784361/251650000000000000000 : ℝ)+2*(4518625115257/1258250000000000 : ℝ)*(3341/12500 : ℝ)=(10018074613895853/10000000000000000 : ℝ) by norm_num, show 1+2*(95476209735795429/25000000000000000000 : ℝ)=(12595476209735795429/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (251621752410366784361/251650000000000000000 : ℝ)*(X 1 0+X 2 0)+(4518625115257/1258250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4321/1024 : ℝ)) (lo := (1563/100000 : ℝ)) (hi := (3341/12500 : ℝ)) (c := (251621752410366784361/251650000000000000000 : ℝ)) (alpha := (4518625115257/1258250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (251621752410366784361/251650000000000000000 : ℝ)*(X 0 1+X 2 1)+(4518625115257/1258250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4321/1024 : ℝ)) (lo := (1563/100000 : ℝ)) (hi := (3341/12500 : ℝ)) (c := (251621752410366784361/251650000000000000000 : ℝ)) (alpha := (4518625115257/1258250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (251621752410366784361/251650000000000000000 : ℝ)*(X 0 2+X 1 2)+(4518625115257/1258250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4321/1024 : ℝ)) (lo := (1563/100000 : ℝ)) (hi := (3341/12500 : ℝ)) (c := (251621752410366784361/251650000000000000000 : ℝ)) (alpha := (4518625115257/1258250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-989657217/5000000000 : ℝ)*X 0 0+(2816640131/5000000000 : ℝ)*X 0 1+(1010833651/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5403640189/10000000000 : ℝ)*X 1 0+(-2287820407/10000000000 : ℝ)*X 1 1+(315885577/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2701820203/5000000000 : ℝ)*X 2 0+(2527084219/5000000000 : ℝ)*X 2 1+(-2287821139/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((857746693/2000000000 : ℝ)*X 0 0+(929416719/2500000000 : ℝ)*X 0 1+(2469894239/5000000000 : ℝ)*X 0 2+(857746693/2000000000 : ℝ)*X 1 0+(929416719/2500000000 : ℝ)*X 1 1+(2469894239/5000000000 : ℝ)*X 1 2+(857746693/2000000000 : ℝ)*X 2 0+(929416719/2500000000 : ℝ)*X 2 1+(2469894239/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-989907781/5000000000 : ℝ)*X 0 0+(5061324039/10000000000 : ℝ)*X 0 1+(2812998159/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1050624103/2000000000 : ℝ)*X 1 0+(-857996567/5000000000 : ℝ)*X 1 1+(5625996389/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((656640051/1250000000 : ℝ)*X 2 0+(5625996477/10000000000 : ℝ)*X 2 1+(-857996579/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2144895841/5000000000 : ℝ)*X 0 0+(615586109/1250000000 : ℝ)*X 0 1+(233314727/625000000 : ℝ)*X 0 2+(2144895841/5000000000 : ℝ)*X 1 0+(615586109/1250000000 : ℝ)*X 1 1+(233314727/625000000 : ℝ)*X 1 2+(2144895841/5000000000 : ℝ)*X 2 0+(615586109/1250000000 : ℝ)*X 2 1+(233314727/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (49188538699959304699104705573/6291250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9747633/50000000000000 : ℝ)*(base16) + (300553249/25000000000000 : ℝ)*(base19) + (1295711821/100000000000000 : ℝ)*(base23) + (15733/625000000000 : ℝ)*(upper2) + (234278469/100000000000000 : ℝ)*(upper3) + (636264674920031/50000000000000 : ℝ)*(major0) + (636264674920031/50000000000000 : ℝ)*(major1) + (636264674920031/50000000000000 : ℝ)*(major2) + (172679317182387/10000000000000 : ℝ)*(sp0) + (43170025731553/2500000000000 : ℝ)*(sp1) + (863400477629281/50000000000000 : ℝ)*(sp2) + (409126021262657/50000000000000 : ℝ)*(sp3) + (567446657/6250000000000 : ℝ)*(sp4) + (4145565629/100000000000000 : ℝ)*(sp7) + (409128094045471/50000000000000 : ℝ)*(f.failure) + (863401125485191/50000000000000 : ℝ)*(f.sum) + (211551645642733/31456250000000000000000000000 : ℝ)*base66 + (5626365696560164809/12582500000000000000000000000000000 : ℝ)*base68 + (13654065475294835191/12582500000000000000000000000000000 : ℝ)*base69 + (50595418033720164809/12582500000000000000000000000000000 : ℝ)*base72 + (43097923558883/31456250000000000000000000000 : ℝ)*base74 + (48038235870939835191/12582500000000000000000000000000000 : ℝ)*base75 + (140602010211810164809/12582500000000000000000000000000000 : ℝ)*base78 + (106155636642020164809/12582500000000000000000000000000000 : ℝ)*base80 + (141894315618859/62912500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (50080141/5000000000000000000000 : ℝ)*base90 + (50080141/5000000000000000000000 : ℝ)*base92 + (50080141/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6535883434394378107003646277/2516500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13886931/50000000000000 : ℝ)*(base1) + (537435431/100000000000000 : ℝ)*(base19) + (125116733/25000000000000 : ℝ)*(base23) + (32163167/50000000000000 : ℝ)*(upper3) + (53952439/100000000000000 : ℝ)*(upper5) + (261010890361919/20000000000000 : ℝ)*(major0) + (261010890361919/20000000000000 : ℝ)*(major1) + (261010890361919/20000000000000 : ℝ)*(major2) + (2932638197/100000000000000 : ℝ)*(sp1) + (2901342887/100000000000000 : ℝ)*(sp2) + (1770938509672987/100000000000000 : ℝ)*(sp4) + (1770935011825497/100000000000000 : ℝ)*(sp5) + (885467540044653/50000000000000 : ℝ)*(sp6) + (419585153686237/50000000000000 : ℝ)*(sp7) + (26224072973323/3125000000000 : ℝ)*(f.failure) + (14167507855193/800000000000 : ℝ)*(f.sum) + (2028206645417/786406250000000000000000000 : ℝ)*base66 + (2195408683937251241/5033000000000000000000000000000000 : ℝ)*base68 + (7938623432166251241/5033000000000000000000000000000000 : ℝ)*base70 + (1057481449107748759/5033000000000000000000000000000000 : ℝ)*base71 + (118180641494549/25165000000000000000000000000 : ℝ)*base74 + (8137040251809251241/5033000000000000000000000000000000 : ℝ)*base76 + (17824524439301748759/5033000000000000000000000000000000 : ℝ)*base77 + (15082611411112251241/5033000000000000000000000000000000 : ℝ)*base80 + (145425563371589/25165000000000000000000000000 : ℝ)*base82 + (493033/312500000000000000000 : ℝ)*base90 + (493033/312500000000000000000 : ℝ)*base92 + (493033/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1362_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155517229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3341/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1563/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7073/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19313/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1362_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1362_s2_0 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-252219977/1250000000 : ℝ)*x 0 + (1368598981/2500000000 : ℝ)*x 1 + (5188398209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (252219977/1250000000 : ℝ)^2161 ≤ (3068863415289/25000000000000 : ℝ)^1649 := by
    have hnat : (252219977 : ℕ)^2161*25000000000000^1649 ≤ 3068863415289^1649*1250000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252219977 1250000000 3068863415289 25000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1368598981/2500000000 : ℝ)^2161 ≤ (45403767982527/100000000000000 : ℝ)^1649 := by
    have hnat : (1368598981 : ℕ)^2161*100000000000000^1649 ≤ 45403767982527^1649*2500000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368598981 2500000000 45403767982527 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5188398209/10000000000 : ℝ)^2161 ≤ (1692831133591/4000000000000 : ℝ)^1649 := by
    have hnat : (5188398209 : ℕ)^2161*4000000000000^1649 ≤ 1692831133591^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5188398209 10000000000 1692831133591 4000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-252219977/1250000000 : ℝ), (1368598981/2500000000 : ℝ), (5188398209/10000000000 : ℝ)] ![(3068863415289/25000000000000 : ℝ), (45403767982527/100000000000000 : ℝ), (1692831133591/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-252219977/1250000000 : ℝ)|^2161 ≤ (3068863415289/25000000000000 : ℝ)^1649
        have hw : |(-252219977/1250000000 : ℝ)|=(252219977/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1368598981/2500000000 : ℝ)|^2161 ≤ (45403767982527/100000000000000 : ℝ)^1649
        have hw : |(1368598981/2500000000 : ℝ)|=(1368598981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5188398209/10000000000 : ℝ)|^2161 ≤ (1692831133591/4000000000000 : ℝ)^1649
        have hw : |(5188398209/10000000000 : ℝ)|=(5188398209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s2_1 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (335285051/625000000 : ℝ)*x 0 + (-2165378441/10000000000 : ℝ)*x 1 + (5188398537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335285051/625000000 : ℝ)^2161 ≤ (22106852645113/50000000000000 : ℝ)^1649 := by
    have hnat : (335285051 : ℕ)^2161*50000000000000^1649 ≤ 22106852645113^1649*625000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335285051 625000000 22106852645113 50000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2165378441/10000000000 : ℝ)^2161 ≤ (13465512855769/100000000000000 : ℝ)^1649 := by
    have hnat : (2165378441 : ℕ)^2161*100000000000000^1649 ≤ 13465512855769^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165378441 10000000000 13465512855769 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5188398537/10000000000 : ℝ)^2161 ≤ (42320781845907/100000000000000 : ℝ)^1649 := by
    have hnat : (5188398537 : ℕ)^2161*100000000000000^1649 ≤ 42320781845907^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5188398537 10000000000 42320781845907 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335285051/625000000 : ℝ), (-2165378441/10000000000 : ℝ), (5188398537/10000000000 : ℝ)] ![(22106852645113/50000000000000 : ℝ), (13465512855769/100000000000000 : ℝ), (42320781845907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335285051/625000000 : ℝ)|^2161 ≤ (22106852645113/50000000000000 : ℝ)^1649
        have hw : |(335285051/625000000 : ℝ)|=(335285051/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2165378441/10000000000 : ℝ)|^2161 ≤ (13465512855769/100000000000000 : ℝ)^1649
        have hw : |(-2165378441/10000000000 : ℝ)|=(2165378441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5188398537/10000000000 : ℝ)|^2161 ≤ (42320781845907/100000000000000 : ℝ)^1649
        have hw : |(5188398537/10000000000 : ℝ)|=(5188398537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s2_2 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5364560861/10000000000 : ℝ)*x 0 + (5188398479/10000000000 : ℝ)*x 1 + (-2165378457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364560861/10000000000 : ℝ)^2161 ≤ (44213705776263/100000000000000 : ℝ)^1649 := by
    have hnat : (5364560861 : ℕ)^2161*100000000000000^1649 ≤ 44213705776263^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364560861 10000000000 44213705776263 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5188398479/10000000000 : ℝ)^2161 ≤ (132252441331/312500000000 : ℝ)^1649 := by
    have hnat : (5188398479 : ℕ)^2161*312500000000^1649 ≤ 132252441331^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5188398479 10000000000 132252441331 312500000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2165378457/10000000000 : ℝ)^2161 ≤ (13465512986159/100000000000000 : ℝ)^1649 := by
    have hnat : (2165378457 : ℕ)^2161*100000000000000^1649 ≤ 13465512986159^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165378457 10000000000 13465512986159 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364560861/10000000000 : ℝ), (5188398479/10000000000 : ℝ), (-2165378457/10000000000 : ℝ)] ![(44213705776263/100000000000000 : ℝ), (132252441331/312500000000 : ℝ), (13465512986159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364560861/10000000000 : ℝ)|^2161 ≤ (44213705776263/100000000000000 : ℝ)^1649
        have hw : |(5364560861/10000000000 : ℝ)|=(5364560861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5188398479/10000000000 : ℝ)|^2161 ≤ (132252441331/312500000000 : ℝ)^1649
        have hw : |(5188398479/10000000000 : ℝ)|=(5188398479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2165378457/10000000000 : ℝ)|^2161 ≤ (13465512986159/100000000000000 : ℝ)^1649
        have hw : |(-2165378457/10000000000 : ℝ)|=(2165378457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s2_3 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1078919653/2500000000 : ℝ)*x 0 + (804730417/2000000000 : ℝ)*x 1 + (2313602529/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078919653/2500000000 : ℝ)^2161 ≤ (4155708356253/12500000000000 : ℝ)^1649 := by
    have hnat : (1078919653 : ℕ)^2161*12500000000000^1649 ≤ 4155708356253^1649*2500000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078919653 2500000000 4155708356253 12500000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (804730417/2000000000 : ℝ)^2161 ≤ (3032903126551/10000000000000 : ℝ)^1649 := by
    have hnat : (804730417 : ℕ)^2161*10000000000000^1649 ≤ 3032903126551^1649*2000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804730417 2000000000 3032903126551 10000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2313602529/5000000000 : ℝ)^2161 ≤ (36425301865507/100000000000000 : ℝ)^1649 := by
    have hnat : (2313602529 : ℕ)^2161*100000000000000^1649 ≤ 36425301865507^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2313602529 5000000000 36425301865507 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078919653/2500000000 : ℝ), (804730417/2000000000 : ℝ), (2313602529/5000000000 : ℝ)] ![(4155708356253/12500000000000 : ℝ), (3032903126551/10000000000000 : ℝ), (36425301865507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078919653/2500000000 : ℝ)|^2161 ≤ (4155708356253/12500000000000 : ℝ)^1649
        have hw : |(1078919653/2500000000 : ℝ)|=(1078919653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(804730417/2000000000 : ℝ)|^2161 ≤ (3032903126551/10000000000000 : ℝ)^1649
        have hw : |(804730417/2000000000 : ℝ)|=(804730417/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2313602529/5000000000 : ℝ)|^2161 ≤ (36425301865507/100000000000000 : ℝ)^1649
        have hw : |(2313602529/5000000000 : ℝ)|=(2313602529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s2_4 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2017820217/10000000000 : ℝ)*x 0 + (5190153273/10000000000 : ℝ)*x 1 + (1368156343/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2017820217/10000000000 : ℝ)^2161 ≤ (12275935218867/100000000000000 : ℝ)^1649 := by
    have hnat : (2017820217 : ℕ)^2161*100000000000000^1649 ≤ 12275935218867^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017820217 10000000000 12275935218867 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5190153273/10000000000 : ℝ)^2161 ≤ (10584884988689/25000000000000 : ℝ)^1649 := by
    have hnat : (5190153273 : ℕ)^2161*25000000000000^1649 ≤ 10584884988689^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5190153273 10000000000 10584884988689 25000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1368156343/2500000000 : ℝ)^2161 ≤ (9076904961931/20000000000000 : ℝ)^1649 := by
    have hnat : (1368156343 : ℕ)^2161*20000000000000^1649 ≤ 9076904961931^1649*2500000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368156343 2500000000 9076904961931 20000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2017820217/10000000000 : ℝ), (5190153273/10000000000 : ℝ), (1368156343/2500000000 : ℝ)] ![(12275935218867/100000000000000 : ℝ), (10584884988689/25000000000000 : ℝ), (9076904961931/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2017820217/10000000000 : ℝ)|^2161 ≤ (12275935218867/100000000000000 : ℝ)^1649
        have hw : |(-2017820217/10000000000 : ℝ)|=(2017820217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5190153273/10000000000 : ℝ)|^2161 ≤ (10584884988689/25000000000000 : ℝ)^1649
        have hw : |(5190153273/10000000000 : ℝ)|=(5190153273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1368156343/2500000000 : ℝ)|^2161 ≤ (9076904961931/20000000000000 : ℝ)^1649
        have hw : |(1368156343/2500000000 : ℝ)|=(1368156343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s2_5 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2645343647/5000000000 : ℝ)*x 0 + (-75246053/400000000 : ℝ)*x 1 + (2736312661/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2645343647/5000000000 : ℝ)^2161 ≤ (4341752164951/10000000000000 : ℝ)^1649 := by
    have hnat : (2645343647 : ℕ)^2161*10000000000000^1649 ≤ 4341752164951^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2645343647 5000000000 4341752164951 10000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (75246053/400000000 : ℝ)^2161 ≤ (174968032399/1562500000000 : ℝ)^1649 := by
    have hnat : (75246053 : ℕ)^2161*1562500000000^1649 ≤ 174968032399^1649*400000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75246053 400000000 174968032399 1562500000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2736312661/5000000000 : ℝ)^2161 ≤ (45384524266259/100000000000000 : ℝ)^1649 := by
    have hnat : (2736312661 : ℕ)^2161*100000000000000^1649 ≤ 45384524266259^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2736312661 5000000000 45384524266259 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2645343647/5000000000 : ℝ), (-75246053/400000000 : ℝ), (2736312661/5000000000 : ℝ)] ![(4341752164951/10000000000000 : ℝ), (174968032399/1562500000000 : ℝ), (45384524266259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2645343647/5000000000 : ℝ)|^2161 ≤ (4341752164951/10000000000000 : ℝ)^1649
        have hw : |(2645343647/5000000000 : ℝ)|=(2645343647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-75246053/400000000 : ℝ)|^2161 ≤ (174968032399/1562500000000 : ℝ)^1649
        have hw : |(-75246053/400000000 : ℝ)|=(75246053/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2736312661/5000000000 : ℝ)|^2161 ≤ (45384524266259/100000000000000 : ℝ)^1649
        have hw : |(2736312661/5000000000 : ℝ)|=(2736312661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s2_6 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2645343629/5000000000 : ℝ)*x 0 + (43781003/80000000 : ℝ)*x 1 + (-18811513/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2645343629/5000000000 : ℝ)^2161 ≤ (868350425247/2000000000000 : ℝ)^1649 := by
    have hnat : (2645343629 : ℕ)^2161*2000000000000^1649 ≤ 868350425247^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2645343629 5000000000 868350425247 2000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43781003/80000000 : ℝ)^2161 ≤ (22692262421129/50000000000000 : ℝ)^1649 := by
    have hnat : (43781003 : ℕ)^2161*50000000000000^1649 ≤ 22692262421129^1649*80000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43781003 80000000 22692262421129 50000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (18811513/100000000 : ℝ)^2161 ≤ (699872117407/6250000000000 : ℝ)^1649 := by
    have hnat : (18811513 : ℕ)^2161*6250000000000^1649 ≤ 699872117407^1649*100000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18811513 100000000 699872117407 6250000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2645343629/5000000000 : ℝ), (43781003/80000000 : ℝ), (-18811513/100000000 : ℝ)] ![(868350425247/2000000000000 : ℝ), (22692262421129/50000000000000 : ℝ), (699872117407/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2645343629/5000000000 : ℝ)|^2161 ≤ (868350425247/2000000000000 : ℝ)^1649
        have hw : |(2645343629/5000000000 : ℝ)|=(2645343629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(43781003/80000000 : ℝ)|^2161 ≤ (22692262421129/50000000000000 : ℝ)^1649
        have hw : |(43781003/80000000 : ℝ)|=(43781003/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-18811513/100000000 : ℝ)|^2161 ≤ (699872117407/6250000000000 : ℝ)^1649
        have hw : |(-18811513/100000000 : ℝ)|=(18811513/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s2_7 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2157903177/5000000000 : ℝ)*x 0 + (462350181/1000000000 : ℝ)*x 1 + (1006847001/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157903177/5000000000 : ℝ)^2161 ≤ (16623478226121/50000000000000 : ℝ)^1649 := by
    have hnat : (2157903177 : ℕ)^2161*50000000000000^1649 ≤ 16623478226121^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157903177 5000000000 16623478226121 50000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (462350181/1000000000 : ℝ)^2161 ≤ (7277420654809/20000000000000 : ℝ)^1649 := by
    have hnat : (462350181 : ℕ)^2161*20000000000000^1649 ≤ 7277420654809^1649*1000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      462350181 1000000000 7277420654809 20000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1006847001/2500000000 : ℝ)^2161 ≤ (151829701321/500000000000 : ℝ)^1649 := by
    have hnat : (1006847001 : ℕ)^2161*500000000000^1649 ≤ 151829701321^1649*2500000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006847001 2500000000 151829701321 500000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2157903177/5000000000 : ℝ), (462350181/1000000000 : ℝ), (1006847001/2500000000 : ℝ)] ![(16623478226121/50000000000000 : ℝ), (7277420654809/20000000000000 : ℝ), (151829701321/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2157903177/5000000000 : ℝ)|^2161 ≤ (16623478226121/50000000000000 : ℝ)^1649
        have hw : |(2157903177/5000000000 : ℝ)|=(2157903177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(462350181/1000000000 : ℝ)|^2161 ≤ (7277420654809/20000000000000 : ℝ)^1649
        have hw : |(462350181/1000000000 : ℝ)|=(462350181/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1006847001/2500000000 : ℝ)|^2161 ≤ (151829701321/500000000000 : ℝ)^1649
        have hw : |(1006847001/2500000000 : ℝ)|=(1006847001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1362_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155517229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19313/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7073/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (499/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16027/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19313/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7073/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19313/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7073/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19313/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7073/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19313/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7073/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19313/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7073/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19313/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7073/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7073/100000 : ℝ) ^ (4321/1024 : ℝ) ≤ (279686815601817/20000000000000000000 : ℝ) := by
    have hpowers : (7073/100000 : ℝ)^4321 ≤ (279686815601817/20000000000000000000 : ℝ)^1024 := by
      have hnat : (7073 : ℕ)^4321*20000000000000000000^1024 ≤ 279686815601817^1024*100000^4321 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7073 100000 279686815601817 20000000000000000000 4321 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7073/100000 : ℝ)) (X := (279686815601817/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (19313/100000 : ℝ) ^ (4321/1024 : ℝ) ≤ (96935126265861967/100000000000000000000 : ℝ) := by
    have hpowers : (19313/100000 : ℝ)^4321 ≤ (96935126265861967/100000000000000000000 : ℝ)^1024 := by
      have hnat : (19313 : ℕ)^4321*100000000000000000000^1024 ≤ 96935126265861967^1024*100000^4321 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19313 100000 96935126265861967 100000000000000000000 4321 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19313/100000 : ℝ)) (X := (96935126265861967/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000279686815601817/10000000000000000000 : ℝ) ≤ (10000066280084069/10000000000000000 : ℝ) ^ (4321/1024 : ℝ) := by
    have hpowers : (10000279686815601817/10000000000000000000 : ℝ)^1024 ≤ (10000066280084069/10000000000000000 : ℝ)^4321 := by
      have hnat : (10000279686815601817 : ℕ)^1024*10000000000000000^4321 ≤ 10000066280084069^4321*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000279686815601817 10000000000000000000 10000066280084069 10000000000000000 1024 4321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000066280084069/10000000000000000 : ℝ)) (X := (10000279686815601817/10000000000000000000 : ℝ)) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25024583390085967763/25000000000000000000 : ℝ) ≤ (10002329456428729/10000000000000000 : ℝ) ^ (4321/1024 : ℝ) := by
    have hpowers : (25024583390085967763/25000000000000000000 : ℝ)^1024 ≤ (10002329456428729/10000000000000000 : ℝ)^4321 := by
      have hnat : (25024583390085967763 : ℕ)^1024*10000000000000000^4321 ≤ 10002329456428729^4321*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25024583390085967763 25000000000000000000 10002329456428729 10000000000000000 1024 4321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002329456428729/10000000000000000 : ℝ)) (X := (25024583390085967763/25000000000000000000 : ℝ)) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50096935126265861967/50000000000000000000 : ℝ) ≤ (10004592632773389/10000000000000000 : ℝ) ^ (4321/1024 : ℝ) := by
    have hpowers : (50096935126265861967/50000000000000000000 : ℝ)^1024 ≤ (10004592632773389/10000000000000000 : ℝ)^4321 := by
      have hnat : (50096935126265861967 : ℕ)^1024*10000000000000000^4321 ≤ 10004592632773389^4321*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50096935126265861967 50000000000000000000 10004592632773389 10000000000000000 1024 4321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004592632773389/10000000000000000 : ℝ)) (X := (50096935126265861967/50000000000000000000 : ℝ)) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(279686815601817/20000000000000000000 : ℝ) ≤ ((611843981878287221/612000000000000000 : ℝ)+2*(113158817233/61200000000000 : ℝ)*(7073/100000 : ℝ))^(4321/1024 : ℝ) := by
    rw [show (611843981878287221/612000000000000000 : ℝ)+2*(113158817233/61200000000000 : ℝ)*(7073/100000 : ℝ)=(10000066280084069/10000000000000000 : ℝ) by norm_num, show 1+2*(279686815601817/20000000000000000000 : ℝ)=(10000279686815601817/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(96935126265861967/100000000000000000000 : ℝ)+(279686815601817/20000000000000000000 : ℝ) ≤ ((611843981878287221/612000000000000000 : ℝ)+(113158817233/61200000000000 : ℝ)*((19313/100000 : ℝ)+(7073/100000 : ℝ)))^(4321/1024 : ℝ) := by
    rw [show (611843981878287221/612000000000000000 : ℝ)+(113158817233/61200000000000 : ℝ)*((19313/100000 : ℝ)+(7073/100000 : ℝ))=(10002329456428729/10000000000000000 : ℝ) by norm_num, show 1+(96935126265861967/100000000000000000000 : ℝ)+(279686815601817/20000000000000000000 : ℝ)=(25024583390085967763/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(96935126265861967/100000000000000000000 : ℝ) ≤ ((611843981878287221/612000000000000000 : ℝ)+2*(113158817233/61200000000000 : ℝ)*(19313/100000 : ℝ))^(4321/1024 : ℝ) := by
    rw [show (611843981878287221/612000000000000000 : ℝ)+2*(113158817233/61200000000000 : ℝ)*(19313/100000 : ℝ)=(10004592632773389/10000000000000000 : ℝ) by norm_num, show 1+2*(96935126265861967/100000000000000000000 : ℝ)=(50096935126265861967/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (611843981878287221/612000000000000000 : ℝ)*(X 1 0+X 2 0)+(113158817233/61200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4321/1024 : ℝ)) (lo := (7073/100000 : ℝ)) (hi := (19313/100000 : ℝ)) (c := (611843981878287221/612000000000000000 : ℝ)) (alpha := (113158817233/61200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (611843981878287221/612000000000000000 : ℝ)*(X 0 1+X 2 1)+(113158817233/61200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4321/1024 : ℝ)) (lo := (7073/100000 : ℝ)) (hi := (19313/100000 : ℝ)) (c := (611843981878287221/612000000000000000 : ℝ)) (alpha := (113158817233/61200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (611843981878287221/612000000000000000 : ℝ)*(X 0 2+X 1 2)+(113158817233/61200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4321/1024 : ℝ)) (lo := (7073/100000 : ℝ)) (hi := (19313/100000 : ℝ)) (c := (611843981878287221/612000000000000000 : ℝ)) (alpha := (113158817233/61200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-252219977/1250000000 : ℝ)*X 0 0+(1368598981/2500000000 : ℝ)*X 0 1+(5188398209/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((335285051/625000000 : ℝ)*X 1 0+(-2165378441/10000000000 : ℝ)*X 1 1+(5188398537/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5364560861/10000000000 : ℝ)*X 2 0+(5188398479/10000000000 : ℝ)*X 2 1+(-2165378457/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1078919653/2500000000 : ℝ)*X 0 0+(804730417/2000000000 : ℝ)*X 0 1+(2313602529/5000000000 : ℝ)*X 0 2+(1078919653/2500000000 : ℝ)*X 1 0+(804730417/2000000000 : ℝ)*X 1 1+(2313602529/5000000000 : ℝ)*X 1 2+(1078919653/2500000000 : ℝ)*X 2 0+(804730417/2000000000 : ℝ)*X 2 1+(2313602529/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2017820217/10000000000 : ℝ)*X 0 0+(5190153273/10000000000 : ℝ)*X 0 1+(1368156343/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2645343647/5000000000 : ℝ)*X 1 0+(-75246053/400000000 : ℝ)*X 1 1+(2736312661/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2645343629/5000000000 : ℝ)*X 2 0+(43781003/80000000 : ℝ)*X 2 1+(-18811513/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2157903177/5000000000 : ℝ)*X 0 0+(462350181/1000000000 : ℝ)*X 0 1+(1006847001/2500000000 : ℝ)*X 0 2+(2157903177/5000000000 : ℝ)*X 1 0+(462350181/1000000000 : ℝ)*X 1 1+(1006847001/2500000000 : ℝ)*X 1 2+(2157903177/5000000000 : ℝ)*X 2 0+(462350181/1000000000 : ℝ)*X 2 1+(1006847001/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (402418085594548148102473/85000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (711166237/100000000000000 : ℝ)*(base19) + (730415723/100000000000000 : ℝ)*(base23) + (5407997/100000000000000 : ℝ)*(lower2) + (99242971/100000000000000 : ℝ)*(upper3) + (84294247/100000000000000 : ℝ)*(upper5) + (128835551304839/5000000000000 : ℝ)*(major0) + (128835551304839/5000000000000 : ℝ)*(major1) + (128835551304839/5000000000000 : ℝ)*(major2) + (699308799382617/20000000000000 : ℝ)*(sp0) + (17482779341253/500000000000 : ℝ)*(sp1) + (699311169800223/20000000000000 : ℝ)*(sp2) + (828430105968961/50000000000000 : ℝ)*(sp3) + (12582503753/100000000000000 : ℝ)*(sp4) + (5103027779/100000000000000 : ℝ)*(sp7) + (1656865314965701/100000000000000 : ℝ)*(f.failure) + (1748278289708419/50000000000000 : ℝ)*(f.sum) + (71473630433/15300000000000000000000000 : ℝ)*base65 + (6202200773702527/1020000000000000000000000000000 : ℝ)*base68 + (8503231017782527/1020000000000000000000000000000 : ℝ)*base70 + (4579326562077473/1020000000000000000000000000000 : ℝ)*base71 + (293547578207/153000000000000000000000000 : ℝ)*base73 + (12678791063162527/1020000000000000000000000000000 : ℝ)*base76 + (5871461261222527/1020000000000000000000000000000 : ℝ)*base78 + (7692731849222527/1020000000000000000000000000000 : ℝ)*base80 + (323759577913/76500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (49562529/10000000000000000000000 : ℝ)*base89 + (49562529/10000000000000000000000 : ℝ)*base91 + (49562529/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3843249700735172114317/510000000000000000000000000 : ℝ) := by norm_num
    linear_combination (390954619/25000000000000 : ℝ)*(base19) + (1710796331/100000000000000 : ℝ)*(base23) + (176938501/100000000000000 : ℝ)*(upper3) + (35038993/50000000000000 : ℝ)*(lower4) + (126937983/100000000000000 : ℝ)*(upper5) + (1304425763390569/50000000000000 : ℝ)*(major0) + (1304425763390569/50000000000000 : ℝ)*(major1) + (1304425763390569/50000000000000 : ℝ)*(major2) + (3612325727/20000000000000 : ℝ)*(sp1) + (20826873851/100000000000000 : ℝ)*(sp2) + (177008532248193/5000000000000 : ℝ)*(sp4) + (3540151019516749/100000000000000 : ℝ)*(sp5) + (1770074053646839/50000000000000 : ℝ)*(sp6) + (83876607870281/5000000000000 : ℝ)*(sp7) + (83876607870281/5000000000000 : ℝ)*(f.failure) + (177008532248193/5000000000000 : ℝ)*(f.sum) + (4723829470223/1530000000000000000000000000 : ℝ)*base66 + (89940744384129583/10200000000000000000000000000000 : ℝ)*base67 + (12064890299870417/10200000000000000000000000000000 : ℝ)*base70 + (16463379649070417/10200000000000000000000000000000 : ℝ)*base72 + (5761383113377/1530000000000000000000000000 : ℝ)*base73 + (108368863319529583/10200000000000000000000000000000 : ℝ)*base75 + (3187541792870417/10200000000000000000000000000000 : ℝ)*base78 + (123524875774329583/10200000000000000000000000000000 : ℝ)*base79 + (6678743079113/1530000000000000000000000000 : ℝ)*base82 + (2571349/500000000000000000000 : ℝ)*base89 + (2571349/500000000000000000000 : ℝ)*base91 + (2571349/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1362_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155517229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19313/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7073/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (499/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16027/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1362_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1362_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155517229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (499/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16027/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1362_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1362_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1362_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155517229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (499/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16027/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1362_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

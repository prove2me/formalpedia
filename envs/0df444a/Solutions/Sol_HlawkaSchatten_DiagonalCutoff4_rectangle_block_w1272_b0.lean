-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1272_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:20:19.945674+00:00
-- url     : https://prove2.me/submissions/2225c5e6-1926-4424-b3f3-b305c5ad3241

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
theorem support_rectangle_w1272_s0_0 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-231379031/1250000000 : ℝ)*x 0 + (6024545771/10000000000 : ℝ)*x 1 + (2398406683/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (231379031/1250000000 : ℝ)^4233 ≤ (1080547687841/10000000000000 : ℝ)^3209 := by
    have hnat : (231379031 : ℕ)^4233*10000000000000^3209 ≤ 1080547687841^3209*1250000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231379031 1250000000 1080547687841 10000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6024545771/10000000000 : ℝ)^4233 ≤ (51250440143183/100000000000000 : ℝ)^3209 := by
    have hnat : (6024545771 : ℕ)^4233*100000000000000^3209 ≤ 51250440143183^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6024545771 10000000000 51250440143183 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2398406683/5000000000 : ℝ)^4233 ≤ (18972041483553/50000000000000 : ℝ)^3209 := by
    have hnat : (2398406683 : ℕ)^4233*50000000000000^3209 ≤ 18972041483553^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2398406683 5000000000 18972041483553 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-231379031/1250000000 : ℝ), (6024545771/10000000000 : ℝ), (2398406683/5000000000 : ℝ)] ![(1080547687841/10000000000000 : ℝ), (51250440143183/100000000000000 : ℝ), (18972041483553/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-231379031/1250000000 : ℝ)|^4233 ≤ (1080547687841/10000000000000 : ℝ)^3209
        have hw : |(-231379031/1250000000 : ℝ)|=(231379031/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6024545771/10000000000 : ℝ)|^4233 ≤ (51250440143183/100000000000000 : ℝ)^3209
        have hw : |(6024545771/10000000000 : ℝ)|=(6024545771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2398406683/5000000000 : ℝ)|^4233 ≤ (18972041483553/50000000000000 : ℝ)^3209
        have hw : |(2398406683/5000000000 : ℝ)|=(2398406683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s0_1 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1101882629/2000000000 : ℝ)*x 0 + (-2552073661/10000000000 : ℝ)*x 1 + (4796813337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1101882629/2000000000 : ℝ)^4233 ≤ (22775158391739/50000000000000 : ℝ)^3209 := by
    have hnat : (1101882629 : ℕ)^4233*50000000000000^3209 ≤ 22775158391739^3209*2000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101882629 2000000000 22775158391739 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2552073661/10000000000 : ℝ)^4233 ≤ (4126400132761/25000000000000 : ℝ)^3209 := by
    have hnat : (2552073661 : ℕ)^4233*25000000000000^3209 ≤ 4126400132761^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2552073661 10000000000 4126400132761 25000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4796813337/10000000000 : ℝ)^4233 ≤ (37944082664507/100000000000000 : ℝ)^3209 := by
    have hnat : (4796813337 : ℕ)^4233*100000000000000^3209 ≤ 37944082664507^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4796813337 10000000000 37944082664507 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1101882629/2000000000 : ℝ), (-2552073661/10000000000 : ℝ), (4796813337/10000000000 : ℝ)] ![(22775158391739/50000000000000 : ℝ), (4126400132761/25000000000000 : ℝ), (37944082664507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1101882629/2000000000 : ℝ)|^4233 ≤ (22775158391739/50000000000000 : ℝ)^3209
        have hw : |(1101882629/2000000000 : ℝ)|=(1101882629/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2552073661/10000000000 : ℝ)|^4233 ≤ (4126400132761/25000000000000 : ℝ)^3209
        have hw : |(-2552073661/10000000000 : ℝ)|=(2552073661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4796813337/10000000000 : ℝ)|^4233 ≤ (37944082664507/100000000000000 : ℝ)^3209
        have hw : |(4796813337/10000000000 : ℝ)|=(4796813337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s0_2 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5509413163/10000000000 : ℝ)*x 0 + (239840667/500000000 : ℝ)*x 1 + (-638018409/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5509413163/10000000000 : ℝ)^4233 ≤ (22775158489893/50000000000000 : ℝ)^3209 := by
    have hnat : (5509413163 : ℕ)^4233*50000000000000^3209 ≤ 22775158489893^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5509413163 10000000000 22775158489893 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (239840667/500000000 : ℝ)^4233 ≤ (3794408269581/10000000000000 : ℝ)^3209 := by
    have hnat : (239840667 : ℕ)^4233*10000000000000^3209 ≤ 3794408269581^3209*500000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239840667 500000000 3794408269581 10000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (638018409/2500000000 : ℝ)^4233 ≤ (16505600317761/100000000000000 : ℝ)^3209 := by
    have hnat : (638018409 : ℕ)^4233*100000000000000^3209 ≤ 16505600317761^3209*2500000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      638018409 2500000000 16505600317761 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5509413163/10000000000 : ℝ), (239840667/500000000 : ℝ), (-638018409/2500000000 : ℝ)] ![(22775158489893/50000000000000 : ℝ), (3794408269581/10000000000000 : ℝ), (16505600317761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5509413163/10000000000 : ℝ)|^4233 ≤ (22775158489893/50000000000000 : ℝ)^3209
        have hw : |(5509413163/10000000000 : ℝ)|=(5509413163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(239840667/500000000 : ℝ)|^4233 ≤ (3794408269581/10000000000000 : ℝ)^3209
        have hw : |(239840667/500000000 : ℝ)|=(239840667/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-638018409/2500000000 : ℝ)|^4233 ≤ (16505600317761/100000000000000 : ℝ)^3209
        have hw : |(-638018409/2500000000 : ℝ)|=(638018409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s0_3 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (104764937/250000000 : ℝ)*x 0 + (778942143/2500000000 : ℝ)*x 1 + (5621226421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (104764937/250000000 : ℝ)^4233 ≤ (6349992971167/20000000000000 : ℝ)^3209 := by
    have hnat : (104764937 : ℕ)^4233*20000000000000^3209 ≤ 6349992971167^3209*250000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104764937 250000000 6349992971167 20000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (778942143/2500000000 : ℝ)^4233 ≤ (2147635464363/10000000000000 : ℝ)^3209 := by
    have hnat : (778942143 : ℕ)^4233*10000000000000^3209 ≤ 2147635464363^3209*2500000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      778942143 2500000000 2147635464363 10000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5621226421/10000000000 : ℝ)^4233 ≤ (11693420122669/25000000000000 : ℝ)^3209 := by
    have hnat : (5621226421 : ℕ)^4233*25000000000000^3209 ≤ 11693420122669^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5621226421 10000000000 11693420122669 25000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(104764937/250000000 : ℝ), (778942143/2500000000 : ℝ), (5621226421/10000000000 : ℝ)] ![(6349992971167/20000000000000 : ℝ), (2147635464363/10000000000000 : ℝ), (11693420122669/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(104764937/250000000 : ℝ)|^4233 ≤ (6349992971167/20000000000000 : ℝ)^3209
        have hw : |(104764937/250000000 : ℝ)|=(104764937/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(778942143/2500000000 : ℝ)|^4233 ≤ (2147635464363/10000000000000 : ℝ)^3209
        have hw : |(778942143/2500000000 : ℝ)|=(778942143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5621226421/10000000000 : ℝ)|^4233 ≤ (11693420122669/25000000000000 : ℝ)^3209
        have hw : |(5621226421/10000000000 : ℝ)|=(5621226421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s0_4 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-185580223/1000000000 : ℝ)*x 0 + (2414204597/5000000000 : ℝ)*x 1 + (599183229/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (185580223/1000000000 : ℝ)^4233 ≤ (10842222336449/100000000000000 : ℝ)^3209 := by
    have hnat : (185580223 : ℕ)^4233*100000000000000^3209 ≤ 10842222336449^3209*1000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      185580223 1000000000 10842222336449 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2414204597/5000000000 : ℝ)^4233 ≤ (38274114190689/100000000000000 : ℝ)^3209 := by
    have hnat : (2414204597 : ℕ)^4233*100000000000000^3209 ≤ 38274114190689^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2414204597 5000000000 38274114190689 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (599183229/1000000000 : ℝ)^4233 ≤ (25441831731779/50000000000000 : ℝ)^3209 := by
    have hnat : (599183229 : ℕ)^4233*50000000000000^3209 ≤ 25441831731779^3209*1000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      599183229 1000000000 25441831731779 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-185580223/1000000000 : ℝ), (2414204597/5000000000 : ℝ), (599183229/1000000000 : ℝ)] ![(10842222336449/100000000000000 : ℝ), (38274114190689/100000000000000 : ℝ), (25441831731779/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-185580223/1000000000 : ℝ)|^4233 ≤ (10842222336449/100000000000000 : ℝ)^3209
        have hw : |(-185580223/1000000000 : ℝ)|=(185580223/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2414204597/5000000000 : ℝ)|^4233 ≤ (38274114190689/100000000000000 : ℝ)^3209
        have hw : |(2414204597/5000000000 : ℝ)|=(2414204597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(599183229/1000000000 : ℝ)|^4233 ≤ (25441831731779/50000000000000 : ℝ)^3209
        have hw : |(599183229/1000000000 : ℝ)|=(599183229/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s0_5 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2587618709/5000000000 : ℝ)*x 0 + (-1357052233/10000000000 : ℝ)*x 1 + (1198366957/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2587618709/5000000000 : ℝ)^4233 ≤ (10485393090843/25000000000000 : ℝ)^3209 := by
    have hnat : (2587618709 : ℕ)^4233*25000000000000^3209 ≤ 10485393090843^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587618709 5000000000 10485393090843 25000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357052233/10000000000 : ℝ)^4233 ≤ (3587368104183/50000000000000 : ℝ)^3209 := by
    have hnat : (1357052233 : ℕ)^4233*50000000000000^3209 ≤ 3587368104183^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357052233 10000000000 3587368104183 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1198366957/2000000000 : ℝ)^4233 ≤ (2544184570633/5000000000000 : ℝ)^3209 := by
    have hnat : (1198366957 : ℕ)^4233*5000000000000^3209 ≤ 2544184570633^3209*2000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1198366957 2000000000 2544184570633 5000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2587618709/5000000000 : ℝ), (-1357052233/10000000000 : ℝ), (1198366957/2000000000 : ℝ)] ![(10485393090843/25000000000000 : ℝ), (3587368104183/50000000000000 : ℝ), (2544184570633/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2587618709/5000000000 : ℝ)|^4233 ≤ (10485393090843/25000000000000 : ℝ)^3209
        have hw : |(2587618709/5000000000 : ℝ)|=(2587618709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1357052233/10000000000 : ℝ)|^4233 ≤ (3587368104183/50000000000000 : ℝ)^3209
        have hw : |(-1357052233/10000000000 : ℝ)|=(1357052233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1198366957/2000000000 : ℝ)|^4233 ≤ (2544184570633/5000000000000 : ℝ)^3209
        have hw : |(1198366957/2000000000 : ℝ)|=(1198366957/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s0_6 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5175238553/10000000000 : ℝ)*x 0 + (5991832701/10000000000 : ℝ)*x 1 + (-16963173/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5175238553/10000000000 : ℝ)^4233 ≤ (838831689939/2000000000000 : ℝ)^3209 := by
    have hnat : (5175238553 : ℕ)^4233*2000000000000^3209 ≤ 838831689939^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175238553 10000000000 838831689939 2000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5991832701/10000000000 : ℝ)^4233 ≤ (25441834033799/50000000000000 : ℝ)^3209 := by
    have hnat : (5991832701 : ℕ)^4233*50000000000000^3209 ≤ 25441834033799^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5991832701 10000000000 25441834033799 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16963173/125000000 : ℝ)^4233 ≤ (7174747415741/100000000000000 : ℝ)^3209 := by
    have hnat : (16963173 : ℕ)^4233*100000000000000^3209 ≤ 7174747415741^3209*125000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16963173 125000000 7174747415741 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5175238553/10000000000 : ℝ), (5991832701/10000000000 : ℝ), (-16963173/125000000 : ℝ)] ![(838831689939/2000000000000 : ℝ), (25441834033799/50000000000000 : ℝ), (7174747415741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5175238553/10000000000 : ℝ)|^4233 ≤ (838831689939/2000000000000 : ℝ)^3209
        have hw : |(5175238553/10000000000 : ℝ)|=(5175238553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5991832701/10000000000 : ℝ)|^4233 ≤ (25441834033799/50000000000000 : ℝ)^3209
        have hw : |(5991832701/10000000000 : ℝ)|=(5991832701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-16963173/125000000 : ℝ)|^4233 ≤ (7174747415741/100000000000000 : ℝ)^3209
        have hw : |(-16963173/125000000 : ℝ)|=(16963173/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s0_7 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4200334907/10000000000 : ℝ)*x 0 + (1111350889/2000000000 : ℝ)*x 1 + (198907581/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4200334907/10000000000 : ℝ)^4233 ≤ (7961829554961/25000000000000 : ℝ)^3209 := by
    have hnat : (4200334907 : ℕ)^4233*25000000000000^3209 ≤ 7961829554961^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4200334907 10000000000 7961829554961 25000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1111350889/2000000000 : ℝ)^4233 ≤ (23033663212969/50000000000000 : ℝ)^3209 := by
    have hnat : (1111350889 : ℕ)^4233*50000000000000^3209 ≤ 23033663212969^3209*2000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1111350889 2000000000 23033663212969 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (198907581/625000000 : ℝ)^4233 ≤ (22085355334213/100000000000000 : ℝ)^3209 := by
    have hnat : (198907581 : ℕ)^4233*100000000000000^3209 ≤ 22085355334213^3209*625000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198907581 625000000 22085355334213 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4200334907/10000000000 : ℝ), (1111350889/2000000000 : ℝ), (198907581/625000000 : ℝ)] ![(7961829554961/25000000000000 : ℝ), (23033663212969/50000000000000 : ℝ), (22085355334213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4200334907/10000000000 : ℝ)|^4233 ≤ (7961829554961/25000000000000 : ℝ)^3209
        have hw : |(4200334907/10000000000 : ℝ)|=(4200334907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1111350889/2000000000 : ℝ)|^4233 ≤ (23033663212969/50000000000000 : ℝ)^3209
        have hw : |(1111350889/2000000000 : ℝ)|=(1111350889/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(198907581/625000000 : ℝ)|^4233 ≤ (22085355334213/100000000000000 : ℝ)^3209
        have hw : |(198907581/625000000 : ℝ)|=(198907581/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1272_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38008999/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (941/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27321/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8465/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8465 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8465*1^2048 ≤ 0^2048*1^8465 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8465 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8465/2048 : ℝ) ≤ (453131492883528733/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8465 ≤ (453131492883528733/20000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8465*20000000000000000000^2048 ≤ 453131492883528733^2048*5^8465 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 453131492883528733 20000000000000000000 8465 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (453131492883528733/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8465/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8465 := by
      have hnat : (1 : ℕ)^2048*1^8465 ≤ 1^8465*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20453131492883528733/20000000000000000000 : ℝ) ≤ (1005435015484491/1000000000000000 : ℝ) ^ (8465/2048 : ℝ) := by
    have hpowers : (20453131492883528733/20000000000000000000 : ℝ)^2048 ≤ (1005435015484491/1000000000000000 : ℝ)^8465 := by
      have hnat : (20453131492883528733 : ℕ)^2048*1000000000000000^8465 ≤ 1005435015484491^8465*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20453131492883528733 20000000000000000000 1005435015484491 1000000000000000 2048 8465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1005435015484491/1000000000000000 : ℝ)) (X := (20453131492883528733/20000000000000000000 : ℝ)) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10453131492883528733/10000000000000000000 : ℝ) ≤ (505435015484491/500000000000000 : ℝ) ^ (8465/2048 : ℝ) := by
    have hpowers : (10453131492883528733/10000000000000000000 : ℝ)^2048 ≤ (505435015484491/500000000000000 : ℝ)^8465 := by
      have hnat : (10453131492883528733 : ℕ)^2048*500000000000000^8465 ≤ 505435015484491^8465*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10453131492883528733 10000000000000000000 505435015484491 500000000000000 2048 8465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (505435015484491/500000000000000 : ℝ)) (X := (10453131492883528733/10000000000000000000 : ℝ)) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(5435015484491/400000000000000 : ℝ)*(0 : ℝ))^(8465/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(5435015484491/400000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(453131492883528733/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(5435015484491/400000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8465/2048 : ℝ) := by
    rw [show (1 : ℝ)+(5435015484491/400000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1005435015484491/1000000000000000 : ℝ) by norm_num, show 1+(453131492883528733/20000000000000000000 : ℝ)+(0 : ℝ)=(20453131492883528733/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(453131492883528733/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(5435015484491/400000000000000 : ℝ)*(2/5 : ℝ))^(8465/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(5435015484491/400000000000000 : ℝ)*(2/5 : ℝ)=(505435015484491/500000000000000 : ℝ) by norm_num, show 1+2*(453131492883528733/20000000000000000000 : ℝ)=(10453131492883528733/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(5435015484491/400000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8465/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5435015484491/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(5435015484491/400000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8465/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5435015484491/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(5435015484491/400000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8465/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5435015484491/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-231379031/1250000000 : ℝ)*X 0 0+(6024545771/10000000000 : ℝ)*X 0 1+(2398406683/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1101882629/2000000000 : ℝ)*X 1 0+(-2552073661/10000000000 : ℝ)*X 1 1+(4796813337/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5509413163/10000000000 : ℝ)*X 2 0+(239840667/500000000 : ℝ)*X 2 1+(-638018409/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((104764937/250000000 : ℝ)*X 0 0+(778942143/2500000000 : ℝ)*X 0 1+(5621226421/10000000000 : ℝ)*X 0 2+(104764937/250000000 : ℝ)*X 1 0+(778942143/2500000000 : ℝ)*X 1 1+(5621226421/10000000000 : ℝ)*X 1 2+(104764937/250000000 : ℝ)*X 2 0+(778942143/2500000000 : ℝ)*X 2 1+(5621226421/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-185580223/1000000000 : ℝ)*X 0 0+(2414204597/5000000000 : ℝ)*X 0 1+(599183229/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2587618709/5000000000 : ℝ)*X 1 0+(-1357052233/10000000000 : ℝ)*X 1 1+(1198366957/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5175238553/10000000000 : ℝ)*X 2 0+(5991832701/10000000000 : ℝ)*X 2 1+(-16963173/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4200334907/10000000000 : ℝ)*X 0 0+(1111350889/2000000000 : ℝ)*X 0 1+(198907581/625000000 : ℝ)*X 0 2+(4200334907/10000000000 : ℝ)*X 1 0+(1111350889/2000000000 : ℝ)*X 1 1+(198907581/625000000 : ℝ)*X 1 2+(4200334907/10000000000 : ℝ)*X 2 0+(1111350889/2000000000 : ℝ)*X 2 1+(198907581/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28574288858676556872471/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17956181/50000000000000 : ℝ)*(base1) + (34899043/5000000000000 : ℝ)*(base19) + (140128397/20000000000000 : ℝ)*(base23) + (38866549/50000000000000 : ℝ)*(upper3) + (4248689/5000000000000 : ℝ)*(upper5) + (606822420481927/100000000000000 : ℝ)*(major0) + (606822420481927/100000000000000 : ℝ)*(major1) + (606822420481927/100000000000000 : ℝ)*(major2) + (814511800803267/100000000000000 : ℝ)*(sp0) + (407256645783819/50000000000000 : ℝ)*(sp1) + (50907080556657/6250000000000 : ℝ)*(sp2) + (9978241618503/2500000000000 : ℝ)*(sp3) + (2224657593/100000000000000 : ℝ)*(sp4) + (26387881/2500000000000 : ℝ)*(sp7) + (199565378083861/50000000000000 : ℝ)*(f.failure) + (407256994774249/50000000000000 : ℝ)*(f.sum) + (30339740814157/20000000000000000000000000000 : ℝ)*base65 + (187392159265843/40000000000000000000000000000 : ℝ)*base68 + (210540635785843/40000000000000000000000000000 : ℝ)*base70 + (83131657305843/40000000000000000000000000000 : ℝ)*base72 + (52983740145843/20000000000000000000000000000 : ℝ)*base74 + (9854368345843/40000000000000000000000000000 : ℝ)*base76 + (51451704854157/40000000000000000000000000000 : ℝ)*base77 + (267666793494157/40000000000000000000000000000 : ℝ)*base79 + (91231264265843/20000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (7165139/1250000000000000000000 : ℝ)*base89 + (7165139/1250000000000000000000 : ℝ)*base91 + (7165139/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (44966941928942574447399/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (323624913/100000000000000 : ℝ)*(base1) + (39344801/2000000000000 : ℝ)*(base19) + (429551067/20000000000000 : ℝ)*(base23) + (377406259/100000000000000 : ℝ)*(upper3) + (11872701/20000000000000 : ℝ)*(upper5) + (640360219666737/100000000000000 : ℝ)*(major0) + (640360219666737/100000000000000 : ℝ)*(major1) + (640360219666737/100000000000000 : ℝ)*(major2) + (3611970621/100000000000000 : ℝ)*(sp1) + (69764603/2000000000000 : ℝ)*(sp2) + (107441323673681/12500000000000 : ℝ)*(sp4) + (859524686553863/100000000000000 : ℝ)*(sp5) + (17190492595581/2000000000000 : ℝ)*(sp6) + (52648693770551/12500000000000 : ℝ)*(sp7) + (421189873789321/100000000000000 : ℝ)*(f.failure) + (171906053152907/20000000000000 : ℝ)*(f.sum) + (2292191755867/20000000000000000000000000000 : ℝ)*base65 + (45599473195867/40000000000000000000000000000 : ℝ)*base67 + (186866264555867/40000000000000000000000000000 : ℝ)*base69 + (274876658675867/40000000000000000000000000000 : ℝ)*base71 + (98536467924133/20000000000000000000000000000 : ℝ)*base74 + (592753432075867/40000000000000000000000000000 : ℝ)*base75 + (136719845835867/40000000000000000000000000000 : ℝ)*base77 + (160194267675867/40000000000000000000000000000 : ℝ)*base79 + (3945504715867/20000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (3099679/2500000000000000000000 : ℝ)*base89 + (3099679/2500000000000000000000 : ℝ)*base91 + (3099679/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1272_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38008999/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (941/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27321/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1272_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1272_s1_0 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-81847279/400000000 : ℝ)*x 0 + (1416978139/2500000000 : ℝ)*x 1 + (314282919/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (81847279/400000000 : ℝ)^4233 ≤ (12332889120579/100000000000000 : ℝ)^3209 := by
    have hnat : (81847279 : ℕ)^4233*100000000000000^3209 ≤ 12332889120579^3209*400000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81847279 400000000 12332889120579 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1416978139/2500000000 : ℝ)^4233 ≤ (23643395537289/50000000000000 : ℝ)^3209 := by
    have hnat : (1416978139 : ℕ)^4233*50000000000000^3209 ≤ 23643395537289^3209*2500000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1416978139 2500000000 23643395537289 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (314282919/625000000 : ℝ)^4233 ≤ (39433906041/97656250000 : ℝ)^3209 := by
    have hnat : (314282919 : ℕ)^4233*97656250000^3209 ≤ 39433906041^3209*625000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314282919 625000000 39433906041 97656250000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-81847279/400000000 : ℝ), (1416978139/2500000000 : ℝ), (314282919/625000000 : ℝ)] ![(12332889120579/100000000000000 : ℝ), (23643395537289/50000000000000 : ℝ), (39433906041/97656250000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-81847279/400000000 : ℝ)|^4233 ≤ (12332889120579/100000000000000 : ℝ)^3209
        have hw : |(-81847279/400000000 : ℝ)|=(81847279/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1416978139/2500000000 : ℝ)|^4233 ≤ (23643395537289/50000000000000 : ℝ)^3209
        have hw : |(1416978139/2500000000 : ℝ)|=(1416978139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(314282919/625000000 : ℝ)|^4233 ≤ (39433906041/97656250000 : ℝ)^3209
        have hw : |(314282919/625000000 : ℝ)|=(314282919/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s1_1 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5411981353/10000000000 : ℝ)*x 0 + (-597255247/2500000000 : ℝ)*x 1 + (5028527273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5411981353/10000000000 : ℝ)^4233 ≤ (44490738142453/100000000000000 : ℝ)^3209 := by
    have hnat : (5411981353 : ℕ)^4233*100000000000000^3209 ≤ 44490738142453^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411981353 10000000000 44490738142453 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (597255247/2500000000 : ℝ)^4233 ≤ (7564468014729/50000000000000 : ℝ)^3209 := by
    have hnat : (597255247 : ℕ)^4233*50000000000000^3209 ≤ 7564468014729^3209*2500000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      597255247 2500000000 7564468014729 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5028527273/10000000000 : ℝ)^4233 ≤ (40380325813243/100000000000000 : ℝ)^3209 := by
    have hnat : (5028527273 : ℕ)^4233*100000000000000^3209 ≤ 40380325813243^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5028527273 10000000000 40380325813243 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5411981353/10000000000 : ℝ), (-597255247/2500000000 : ℝ), (5028527273/10000000000 : ℝ)] ![(44490738142453/100000000000000 : ℝ), (7564468014729/50000000000000 : ℝ), (40380325813243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5411981353/10000000000 : ℝ)|^4233 ≤ (44490738142453/100000000000000 : ℝ)^3209
        have hw : |(5411981353/10000000000 : ℝ)|=(5411981353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-597255247/2500000000 : ℝ)|^4233 ≤ (7564468014729/50000000000000 : ℝ)^3209
        have hw : |(-597255247/2500000000 : ℝ)|=(597255247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5028527273/10000000000 : ℝ)|^4233 ≤ (40380325813243/100000000000000 : ℝ)^3209
        have hw : |(5028527273/10000000000 : ℝ)|=(5028527273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s1_2 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1352995473/2500000000 : ℝ)*x 0 + (201141077/400000000 : ℝ)*x 1 + (-2389020731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1352995473/2500000000 : ℝ)^4233 ≤ (44490743987401/100000000000000 : ℝ)^3209 := by
    have hnat : (1352995473 : ℕ)^4233*100000000000000^3209 ≤ 44490743987401^3209*2500000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352995473 2500000000 44490743987401 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (201141077/400000000 : ℝ)^4233 ≤ (315471266617/781250000000 : ℝ)^3209 := by
    have hnat : (201141077 : ℕ)^4233*781250000000^3209 ≤ 315471266617^3209*400000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201141077 400000000 315471266617 781250000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2389020731/10000000000 : ℝ)^4233 ≤ (1891116735327/12500000000000 : ℝ)^3209 := by
    have hnat : (2389020731 : ℕ)^4233*12500000000000^3209 ≤ 1891116735327^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2389020731 10000000000 1891116735327 12500000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1352995473/2500000000 : ℝ), (201141077/400000000 : ℝ), (-2389020731/10000000000 : ℝ)] ![(44490743987401/100000000000000 : ℝ), (315471266617/781250000000 : ℝ), (1891116735327/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1352995473/2500000000 : ℝ)|^4233 ≤ (44490743987401/100000000000000 : ℝ)^3209
        have hw : |(1352995473/2500000000 : ℝ)|=(1352995473/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(201141077/400000000 : ℝ)|^4233 ≤ (315471266617/781250000000 : ℝ)^3209
        have hw : |(201141077/400000000 : ℝ)|=(201141077/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2389020731/10000000000 : ℝ)|^4233 ≤ (1891116735327/12500000000000 : ℝ)^3209
        have hw : |(-2389020731/10000000000 : ℝ)|=(2389020731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s1_3 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (6728363/15625000 : ℝ)*x 0 + (1850491467/5000000000 : ℝ)*x 1 + (5005791513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6728363/15625000 : ℝ)^4233 ≤ (32909886763213/100000000000000 : ℝ)^3209 := by
    have hnat : (6728363 : ℕ)^4233*100000000000000^3209 ≤ 32909886763213^3209*15625000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6728363 15625000 32909886763213 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1850491467/5000000000 : ℝ)^4233 ≤ (26950447066693/100000000000000 : ℝ)^3209 := by
    have hnat : (1850491467 : ℕ)^4233*100000000000000^3209 ≤ 26950447066693^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1850491467 5000000000 26950447066693 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5005791513/10000000000 : ℝ)^4233 ≤ (8027933229833/20000000000000 : ℝ)^3209 := by
    have hnat : (5005791513 : ℕ)^4233*20000000000000^3209 ≤ 8027933229833^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5005791513 10000000000 8027933229833 20000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6728363/15625000 : ℝ), (1850491467/5000000000 : ℝ), (5005791513/10000000000 : ℝ)] ![(32909886763213/100000000000000 : ℝ), (26950447066693/100000000000000 : ℝ), (8027933229833/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6728363/15625000 : ℝ)|^4233 ≤ (32909886763213/100000000000000 : ℝ)^3209
        have hw : |(6728363/15625000 : ℝ)|=(6728363/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1850491467/5000000000 : ℝ)|^4233 ≤ (26950447066693/100000000000000 : ℝ)^3209
        have hw : |(1850491467/5000000000 : ℝ)|=(1850491467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5005791513/10000000000 : ℝ)|^4233 ≤ (8027933229833/20000000000000 : ℝ)^3209
        have hw : |(5005791513/10000000000 : ℝ)|=(5005791513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s1_4 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-409364461/2000000000 : ℝ)*x 0 + (2518412149/5000000000 : ℝ)*x 1 + (565945917/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (409364461/2000000000 : ℝ)^4233 ≤ (123379803733/1000000000000 : ℝ)^3209 := by
    have hnat : (409364461 : ℕ)^4233*1000000000000^3209 ≤ 123379803733^3209*2000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409364461 2000000000 123379803733 1000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2518412149/5000000000 : ℝ)^4233 ≤ (1618729480727/4000000000000 : ℝ)^3209 := by
    have hnat : (2518412149 : ℕ)^4233*4000000000000^3209 ≤ 1618729480727^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2518412149 5000000000 1618729480727 4000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (565945917/1000000000 : ℝ)^4233 ≤ (47193782591627/100000000000000 : ℝ)^3209 := by
    have hnat : (565945917 : ℕ)^4233*100000000000000^3209 ≤ 47193782591627^3209*1000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565945917 1000000000 47193782591627 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-409364461/2000000000 : ℝ), (2518412149/5000000000 : ℝ), (565945917/1000000000 : ℝ)] ![(123379803733/1000000000000 : ℝ), (1618729480727/4000000000000 : ℝ), (47193782591627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-409364461/2000000000 : ℝ)|^4233 ≤ (123379803733/1000000000000 : ℝ)^3209
        have hw : |(-409364461/2000000000 : ℝ)|=(409364461/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2518412149/5000000000 : ℝ)|^4233 ≤ (1618729480727/4000000000000 : ℝ)^3209
        have hw : |(2518412149/5000000000 : ℝ)|=(2518412149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(565945917/1000000000 : ℝ)|^4233 ≤ (47193782591627/100000000000000 : ℝ)^3209
        have hw : |(565945917/1000000000 : ℝ)|=(565945917/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s1_5 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5247018357/10000000000 : ℝ)*x 0 + (-219761051/1250000000 : ℝ)*x 1 + (2829729879/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5247018357/10000000000 : ℝ)^4233 ≤ (10677657611829/25000000000000 : ℝ)^3209 := by
    have hnat : (5247018357 : ℕ)^4233*25000000000000^3209 ≤ 10677657611829^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247018357 10000000000 10677657611829 25000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (219761051/1250000000 : ℝ)^4233 ≤ (10095580485149/100000000000000 : ℝ)^3209 := by
    have hnat : (219761051 : ℕ)^4233*100000000000000^3209 ≤ 10095580485149^3209*1250000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219761051 1250000000 10095580485149 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2829729879/5000000000 : ℝ)^4233 ≤ (11798447264891/25000000000000 : ℝ)^3209 := by
    have hnat : (2829729879 : ℕ)^4233*25000000000000^3209 ≤ 11798447264891^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2829729879 5000000000 11798447264891 25000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5247018357/10000000000 : ℝ), (-219761051/1250000000 : ℝ), (2829729879/5000000000 : ℝ)] ![(10677657611829/25000000000000 : ℝ), (10095580485149/100000000000000 : ℝ), (11798447264891/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5247018357/10000000000 : ℝ)|^4233 ≤ (10677657611829/25000000000000 : ℝ)^3209
        have hw : |(5247018357/10000000000 : ℝ)|=(5247018357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-219761051/1250000000 : ℝ)|^4233 ≤ (10095580485149/100000000000000 : ℝ)^3209
        have hw : |(-219761051/1250000000 : ℝ)|=(219761051/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2829729879/5000000000 : ℝ)|^4233 ≤ (11798447264891/25000000000000 : ℝ)^3209
        have hw : |(2829729879/5000000000 : ℝ)|=(2829729879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s1_6 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (163969321/312500000 : ℝ)*x 0 + (1414864853/2500000000 : ℝ)*x 1 + (-1758089029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (163969321/312500000 : ℝ)^4233 ≤ (42710629534631/100000000000000 : ℝ)^3209 := by
    have hnat : (163969321 : ℕ)^4233*100000000000000^3209 ≤ 42710629534631^3209*312500000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163969321 312500000 42710629534631 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1414864853/2500000000 : ℝ)^4233 ≤ (47193785253601/100000000000000 : ℝ)^3209 := by
    have hnat : (1414864853 : ℕ)^4233*100000000000000^3209 ≤ 47193785253601^3209*2500000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1414864853 2500000000 47193785253601 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1758089029/10000000000 : ℝ)^4233 ≤ (5047792594539/50000000000000 : ℝ)^3209 := by
    have hnat : (1758089029 : ℕ)^4233*50000000000000^3209 ≤ 5047792594539^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1758089029 10000000000 5047792594539 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(163969321/312500000 : ℝ), (1414864853/2500000000 : ℝ), (-1758089029/10000000000 : ℝ)] ![(42710629534631/100000000000000 : ℝ), (47193785253601/100000000000000 : ℝ), (5047792594539/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(163969321/312500000 : ℝ)|^4233 ≤ (42710629534631/100000000000000 : ℝ)^3209
        have hw : |(163969321/312500000 : ℝ)|=(163969321/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1414864853/2500000000 : ℝ)|^4233 ≤ (47193785253601/100000000000000 : ℝ)^3209
        have hw : |(1414864853/2500000000 : ℝ)|=(1414864853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1758089029/10000000000 : ℝ)|^4233 ≤ (5047792594539/50000000000000 : ℝ)^3209
        have hw : |(-1758089029/10000000000 : ℝ)|=(1758089029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s1_7 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4307458751/10000000000 : ℝ)*x 0 + (4988858713/10000000000 : ℝ)*x 1 + (3718234657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4307458751/10000000000 : ℝ)^4233 ≤ (16461528946799/50000000000000 : ℝ)^3209 := by
    have hnat : (4307458751 : ℕ)^4233*50000000000000^3209 ≤ 16461528946799^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4307458751 10000000000 16461528946799 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4988858713/10000000000 : ℝ)^4233 ≤ (2497541102023/6250000000000 : ℝ)^3209 := by
    have hnat : (4988858713 : ℕ)^4233*6250000000000^3209 ≤ 2497541102023^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4988858713 10000000000 2497541102023 6250000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3718234657/10000000000 : ℝ)^4233 ≤ (13558142228777/50000000000000 : ℝ)^3209 := by
    have hnat : (3718234657 : ℕ)^4233*50000000000000^3209 ≤ 13558142228777^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3718234657 10000000000 13558142228777 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4307458751/10000000000 : ℝ), (4988858713/10000000000 : ℝ), (3718234657/10000000000 : ℝ)] ![(16461528946799/50000000000000 : ℝ), (2497541102023/6250000000000 : ℝ), (13558142228777/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4307458751/10000000000 : ℝ)|^4233 ≤ (16461528946799/50000000000000 : ℝ)^3209
        have hw : |(4307458751/10000000000 : ℝ)|=(4307458751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4988858713/10000000000 : ℝ)|^4233 ≤ (2497541102023/6250000000000 : ℝ)^3209
        have hw : |(4988858713/10000000000 : ℝ)|=(4988858713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3718234657/10000000000 : ℝ)|^4233 ≤ (13558142228777/50000000000000 : ℝ)^3209
        have hw : |(3718234657/10000000000 : ℝ)|=(3718234657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1272_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38008999/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27321/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (941/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (397/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19869/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27321/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (941/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27321/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (941/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27321/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (941/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27321/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (941/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27321/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (941/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27321/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (941/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (941/100000 : ℝ) ^ (8465/2048 : ℝ) ≤ (420955712473/100000000000000000000 : ℝ) := by
    have hpowers : (941/100000 : ℝ)^8465 ≤ (420955712473/100000000000000000000 : ℝ)^2048 := by
      have hnat : (941 : ℕ)^8465*100000000000000000000^2048 ≤ 420955712473^2048*100000^8465 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        941 100000 420955712473 100000000000000000000 8465 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (941/100000 : ℝ)) (X := (420955712473/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (27321/100000 : ℝ) ^ (8465/2048 : ℝ) ≤ (9373481276642257/2000000000000000000 : ℝ) := by
    have hpowers : (27321/100000 : ℝ)^8465 ≤ (9373481276642257/2000000000000000000 : ℝ)^2048 := by
      have hnat : (27321 : ℕ)^8465*2000000000000000000^2048 ≤ 9373481276642257^2048*100000^8465 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27321 100000 9373481276642257 2000000000000000000 8465 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27321/100000 : ℝ)) (X := (9373481276642257/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000420955712473/50000000000000000000 : ℝ) ≤ (5000000010184493/5000000000000000 : ℝ) ^ (8465/2048 : ℝ) := by
    have hpowers : (50000000420955712473/50000000000000000000 : ℝ)^2048 ≤ (5000000010184493/5000000000000000 : ℝ)^8465 := by
      have hnat : (50000000420955712473 : ℕ)^2048*5000000000000000^8465 ≤ 5000000010184493^8465*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000420955712473 50000000000000000000 5000000010184493 5000000000000000 2048 8465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000010184493/5000000000000000 : ℝ)) (X := (50000000420955712473/50000000000000000000 : ℝ)) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100468674484787825323/100000000000000000000 : ℝ) ≤ (10011318900431021/10000000000000000 : ℝ) ^ (8465/2048 : ℝ) := by
    have hpowers : (100468674484787825323/100000000000000000000 : ℝ)^2048 ≤ (10011318900431021/10000000000000000 : ℝ)^8465 := by
      have hnat : (100468674484787825323 : ℕ)^2048*10000000000000000^8465 ≤ 10011318900431021^8465*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100468674484787825323 100000000000000000000 10011318900431021 10000000000000000 2048 8465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10011318900431021/10000000000000000 : ℝ)) (X := (100468674484787825323/100000000000000000000 : ℝ)) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (1009373481276642257/1000000000000000000 : ℝ) ≤ (39150928830051/39062500000000 : ℝ) ^ (8465/2048 : ℝ) := by
    have hpowers : (1009373481276642257/1000000000000000000 : ℝ)^2048 ≤ (39150928830051/39062500000000 : ℝ)^8465 := by
      have hnat : (1009373481276642257 : ℕ)^2048*39062500000000^8465 ≤ 39150928830051^8465*1000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1009373481276642257 1000000000000000000 39150928830051 39062500000000 2048 8465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (39150928830051/39062500000000 : ℝ)) (X := (1009373481276642257/1000000000000000000 : ℝ)) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(420955712473/100000000000000000000 : ℝ) ≤ ((26377869840505710081/26380000000000000000 : ℝ)+2*(2263776012407/527600000000000 : ℝ)*(941/100000 : ℝ))^(8465/2048 : ℝ) := by
    rw [show (26377869840505710081/26380000000000000000 : ℝ)+2*(2263776012407/527600000000000 : ℝ)*(941/100000 : ℝ)=(5000000010184493/5000000000000000 : ℝ) by norm_num, show 1+2*(420955712473/100000000000000000000 : ℝ)=(50000000420955712473/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9373481276642257/2000000000000000000 : ℝ)+(420955712473/100000000000000000000 : ℝ) ≤ ((26377869840505710081/26380000000000000000 : ℝ)+(2263776012407/527600000000000 : ℝ)*((27321/100000 : ℝ)+(941/100000 : ℝ)))^(8465/2048 : ℝ) := by
    rw [show (26377869840505710081/26380000000000000000 : ℝ)+(2263776012407/527600000000000 : ℝ)*((27321/100000 : ℝ)+(941/100000 : ℝ))=(10011318900431021/10000000000000000 : ℝ) by norm_num, show 1+(9373481276642257/2000000000000000000 : ℝ)+(420955712473/100000000000000000000 : ℝ)=(100468674484787825323/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9373481276642257/2000000000000000000 : ℝ) ≤ ((26377869840505710081/26380000000000000000 : ℝ)+2*(2263776012407/527600000000000 : ℝ)*(27321/100000 : ℝ))^(8465/2048 : ℝ) := by
    rw [show (26377869840505710081/26380000000000000000 : ℝ)+2*(2263776012407/527600000000000 : ℝ)*(27321/100000 : ℝ)=(39150928830051/39062500000000 : ℝ) by norm_num, show 1+2*(9373481276642257/2000000000000000000 : ℝ)=(1009373481276642257/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26377869840505710081/26380000000000000000 : ℝ)*(X 1 0+X 2 0)+(2263776012407/527600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8465/2048 : ℝ)) (lo := (941/100000 : ℝ)) (hi := (27321/100000 : ℝ)) (c := (26377869840505710081/26380000000000000000 : ℝ)) (alpha := (2263776012407/527600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26377869840505710081/26380000000000000000 : ℝ)*(X 0 1+X 2 1)+(2263776012407/527600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8465/2048 : ℝ)) (lo := (941/100000 : ℝ)) (hi := (27321/100000 : ℝ)) (c := (26377869840505710081/26380000000000000000 : ℝ)) (alpha := (2263776012407/527600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26377869840505710081/26380000000000000000 : ℝ)*(X 0 2+X 1 2)+(2263776012407/527600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8465/2048 : ℝ)) (lo := (941/100000 : ℝ)) (hi := (27321/100000 : ℝ)) (c := (26377869840505710081/26380000000000000000 : ℝ)) (alpha := (2263776012407/527600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-81847279/400000000 : ℝ)*X 0 0+(1416978139/2500000000 : ℝ)*X 0 1+(314282919/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5411981353/10000000000 : ℝ)*X 1 0+(-597255247/2500000000 : ℝ)*X 1 1+(5028527273/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1352995473/2500000000 : ℝ)*X 2 0+(201141077/400000000 : ℝ)*X 2 1+(-2389020731/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((6728363/15625000 : ℝ)*X 0 0+(1850491467/5000000000 : ℝ)*X 0 1+(5005791513/10000000000 : ℝ)*X 0 2+(6728363/15625000 : ℝ)*X 1 0+(1850491467/5000000000 : ℝ)*X 1 1+(5005791513/10000000000 : ℝ)*X 1 2+(6728363/15625000 : ℝ)*X 2 0+(1850491467/5000000000 : ℝ)*X 2 1+(5005791513/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-409364461/2000000000 : ℝ)*X 0 0+(2518412149/5000000000 : ℝ)*X 0 1+(565945917/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5247018357/10000000000 : ℝ)*X 1 0+(-219761051/1250000000 : ℝ)*X 1 1+(2829729879/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((163969321/312500000 : ℝ)*X 2 0+(1414864853/2500000000 : ℝ)*X 2 1+(-1758089029/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4307458751/10000000000 : ℝ)*X 0 0+(4988858713/10000000000 : ℝ)*X 0 1+(3718234657/10000000000 : ℝ)*X 0 2+(4307458751/10000000000 : ℝ)*X 1 0+(4988858713/10000000000 : ℝ)*X 1 1+(3718234657/10000000000 : ℝ)*X 1 2+(4307458751/10000000000 : ℝ)*X 2 0+(4988858713/10000000000 : ℝ)*X 2 1+(3718234657/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (413349456895870255725312897/329750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (59022163/12500000000000 : ℝ)*(base19) + (299105917/50000000000000 : ℝ)*(base23) + (8085739/25000000000000 : ℝ)*(upper3) + (8045181/50000000000000 : ℝ)*(upper4) + (73224557/50000000000000 : ℝ)*(upper5) + (291301076361993/25000000000000 : ℝ)*(major0) + (291301076361993/25000000000000 : ℝ)*(major1) + (291301076361993/25000000000000 : ℝ)*(major2) + (391000916621387/25000000000000 : ℝ)*(sp0) + (1564007812722883/100000000000000 : ℝ)*(sp1) + (1564007686688353/100000000000000 : ℝ)*(sp2) + (766398254348823/100000000000000 : ℝ)*(sp3) + (4618414639/100000000000000 : ℝ)*(sp4) + (2029862801/100000000000000 : ℝ)*(sp7) + (95800035526453/12500000000000 : ℝ)*(f.failure) + (1564008284900187/100000000000000 : ℝ)*(f.sum) + (23687324374869/6595000000000000000000000000 : ℝ)*base66 + (8033974273824598567/659500000000000000000000000000000 : ℝ)*base68 + (2975501098018098567/659500000000000000000000000000000 : ℝ)*base70 + (5898698398772098567/659500000000000000000000000000000 : ℝ)*base72 + (19316894183247/3297500000000000000000000000 : ℝ)*base74 + (6970636446119598567/659500000000000000000000000000000 : ℝ)*base76 + (3874629044003598567/659500000000000000000000000000000 : ℝ)*base78 + (8883783165017098567/659500000000000000000000000000000 : ℝ)*base80 + (700090671349/412187500000000000000000000 : ℝ)*base82 + (4050547/312500000000000000000 : ℝ)*base89 + (4050547/312500000000000000000 : ℝ)*base91 + (4050547/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32469733889251697349737571/5152343750000000000000000000000 : ℝ) := by norm_num
    linear_combination (583459931/50000000000000 : ℝ)*(base19) + (278666011/25000000000000 : ℝ)*(base23) + (6136317/100000000000000 : ℝ)*(upper2) + (92072459/50000000000000 : ℝ)*(upper3) + (13378487/10000000000000 : ℝ)*(upper5) + (18696032421819/1562500000000 : ℝ)*(major0) + (18696032421819/1562500000000 : ℝ)*(major1) + (18696032421819/1562500000000 : ℝ)*(major2) + (3303037007/50000000000000 : ℝ)*(sp1) + (215980663/4000000000000 : ℝ)*(sp2) + (1606076952374721/100000000000000 : ℝ)*(sp4) + (321213835876169/20000000000000 : ℝ)*(sp5) + (803035219097051/50000000000000 : ℝ)*(sp6) + (49188436722101/6250000000000 : ℝ)*(sp7) + (49188436722101/6250000000000 : ℝ)*(f.failure) + (1606076952374721/100000000000000 : ℝ)*(f.sum) + (5372491450717/6595000000000000000000000000 : ℝ)*base66 + (343940414627619839/41218750000000000000000000000000 : ℝ)*base67 + (408012591025630161/41218750000000000000000000000000 : ℝ)*base70 + (237631381874973911/41218750000000000000000000000000 : ℝ)*base72 + (1452591018619/206093750000000000000000000 : ℝ)*base73 + (179227002528067661/41218750000000000000000000000000 : ℝ)*base76 + (213537334056317661/41218750000000000000000000000000 : ℝ)*base78 + (96453036468598911/41218750000000000000000000000000 : ℝ)*base80 + (22816957065927/6595000000000000000000000000 : ℝ)*base82 + (186899/156250000000000000000 : ℝ)*base89 + (186899/156250000000000000000 : ℝ)*base91 + (186899/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1272_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38008999/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27321/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (941/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (397/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19869/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1272_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1272_s2_0 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2092696897/10000000000 : ℝ)*x 0 + (5487600583/10000000000 : ℝ)*x 1 + (5179147311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2092696897/10000000000 : ℝ)^4233 ≤ (12704044481913/100000000000000 : ℝ)^3209 := by
    have hnat : (2092696897 : ℕ)^4233*100000000000000^3209 ≤ 12704044481913^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092696897 10000000000 12704044481913 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5487600583/10000000000 : ℝ)^4233 ≤ (45312579870443/100000000000000 : ℝ)^3209 := by
    have hnat : (5487600583 : ℕ)^4233*100000000000000^3209 ≤ 45312579870443^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5487600583 10000000000 45312579870443 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5179147311/10000000000 : ℝ)^4233 ≤ (20991687813631/50000000000000 : ℝ)^3209 := by
    have hnat : (5179147311 : ℕ)^4233*50000000000000^3209 ≤ 20991687813631^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179147311 10000000000 20991687813631 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2092696897/10000000000 : ℝ), (5487600583/10000000000 : ℝ), (5179147311/10000000000 : ℝ)] ![(12704044481913/100000000000000 : ℝ), (45312579870443/100000000000000 : ℝ), (20991687813631/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2092696897/10000000000 : ℝ)|^4233 ≤ (12704044481913/100000000000000 : ℝ)^3209
        have hw : |(-2092696897/10000000000 : ℝ)|=(2092696897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5487600583/10000000000 : ℝ)|^4233 ≤ (45312579870443/100000000000000 : ℝ)^3209
        have hw : |(5487600583/10000000000 : ℝ)|=(5487600583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5179147311/10000000000 : ℝ)|^4233 ≤ (20991687813631/50000000000000 : ℝ)^3209
        have hw : |(5179147311/10000000000 : ℝ)|=(5179147311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s2_1 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2684219891/5000000000 : ℝ)*x 0 + (-450460849/2000000000 : ℝ)*x 1 + (1035829521/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684219891/5000000000 : ℝ)^4233 ≤ (11004794497157/25000000000000 : ℝ)^3209 := by
    have hnat : (2684219891 : ℕ)^4233*25000000000000^3209 ≤ 11004794497157^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684219891 5000000000 11004794497157 25000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (450460849/2000000000 : ℝ)^4233 ≤ (6998721613011/50000000000000 : ℝ)^3209 := by
    have hnat : (450460849 : ℕ)^4233*50000000000000^3209 ≤ 6998721613011^3209*2000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450460849 2000000000 6998721613011 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1035829521/2000000000 : ℝ)^4233 ≤ (4198337877099/10000000000000 : ℝ)^3209 := by
    have hnat : (1035829521 : ℕ)^4233*10000000000000^3209 ≤ 4198337877099^3209*2000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035829521 2000000000 4198337877099 10000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684219891/5000000000 : ℝ), (-450460849/2000000000 : ℝ), (1035829521/2000000000 : ℝ)] ![(11004794497157/25000000000000 : ℝ), (6998721613011/50000000000000 : ℝ), (4198337877099/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684219891/5000000000 : ℝ)|^4233 ≤ (11004794497157/25000000000000 : ℝ)^3209
        have hw : |(2684219891/5000000000 : ℝ)|=(2684219891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-450460849/2000000000 : ℝ)|^4233 ≤ (6998721613011/50000000000000 : ℝ)^3209
        have hw : |(-450460849/2000000000 : ℝ)|=(450460849/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1035829521/2000000000 : ℝ)|^4233 ≤ (4198337877099/10000000000000 : ℝ)^3209
        have hw : |(1035829521/2000000000 : ℝ)|=(1035829521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s2_2 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (671054969/1250000000 : ℝ)*x 0 + (2589573787/5000000000 : ℝ)*x 1 + (-90092173/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671054969/1250000000 : ℝ)^4233 ≤ (2751198604009/6250000000000 : ℝ)^3209 := by
    have hnat : (671054969 : ℕ)^4233*6250000000000^3209 ≤ 2751198604009^3209*1250000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671054969 1250000000 2751198604009 6250000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2589573787/5000000000 : ℝ)^4233 ≤ (41983378439509/100000000000000 : ℝ)^3209 := by
    have hnat : (2589573787 : ℕ)^4233*100000000000000^3209 ≤ 41983378439509^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589573787 5000000000 41983378439509 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90092173/400000000 : ℝ)^4233 ≤ (13997443881851/100000000000000 : ℝ)^3209 := by
    have hnat : (90092173 : ℕ)^4233*100000000000000^3209 ≤ 13997443881851^3209*400000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90092173 400000000 13997443881851 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671054969/1250000000 : ℝ), (2589573787/5000000000 : ℝ), (-90092173/400000000 : ℝ)] ![(2751198604009/6250000000000 : ℝ), (41983378439509/100000000000000 : ℝ), (13997443881851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671054969/1250000000 : ℝ)|^4233 ≤ (2751198604009/6250000000000 : ℝ)^3209
        have hw : |(671054969/1250000000 : ℝ)|=(671054969/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2589573787/5000000000 : ℝ)|^4233 ≤ (41983378439509/100000000000000 : ℝ)^3209
        have hw : |(2589573787/5000000000 : ℝ)|=(2589573787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-90092173/400000000 : ℝ)|^4233 ≤ (13997443881851/100000000000000 : ℝ)^3209
        have hw : |(-90092173/400000000 : ℝ)|=(90092173/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s2_3 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1084586149/2500000000 : ℝ)*x 0 + (1008648207/2500000000 : ℝ)*x 1 + (4664058739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1084586149/2500000000 : ℝ)^4233 ≤ (16617406234303/50000000000000 : ℝ)^3209 := by
    have hnat : (1084586149 : ℕ)^4233*50000000000000^3209 ≤ 16617406234303^3209*2500000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084586149 2500000000 16617406234303 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1008648207/2500000000 : ℝ)^4233 ≤ (6040034245527/20000000000000 : ℝ)^3209 := by
    have hnat : (1008648207 : ℕ)^4233*20000000000000^3209 ≤ 6040034245527^3209*2500000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008648207 2500000000 6040034245527 20000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4664058739/10000000000 : ℝ)^4233 ≤ (36565016285131/100000000000000 : ℝ)^3209 := by
    have hnat : (4664058739 : ℕ)^4233*100000000000000^3209 ≤ 36565016285131^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4664058739 10000000000 36565016285131 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1084586149/2500000000 : ℝ), (1008648207/2500000000 : ℝ), (4664058739/10000000000 : ℝ)] ![(16617406234303/50000000000000 : ℝ), (6040034245527/20000000000000 : ℝ), (36565016285131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1084586149/2500000000 : ℝ)|^4233 ≤ (16617406234303/50000000000000 : ℝ)^3209
        have hw : |(1084586149/2500000000 : ℝ)|=(1084586149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1008648207/2500000000 : ℝ)|^4233 ≤ (6040034245527/20000000000000 : ℝ)^3209
        have hw : |(1008648207/2500000000 : ℝ)|=(1008648207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4664058739/10000000000 : ℝ)|^4233 ≤ (36565016285131/100000000000000 : ℝ)^3209
        have hw : |(4664058739/10000000000 : ℝ)|=(4664058739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s2_4 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1046384549/5000000000 : ℝ)*x 0 + (5181088331/10000000000 : ℝ)*x 1 + (34285261/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1046384549/5000000000 : ℝ)^4233 ≤ (12704622657607/100000000000000 : ℝ)^3209 := by
    have hnat : (1046384549 : ℕ)^4233*100000000000000^3209 ≤ 12704622657607^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046384549 5000000000 12704622657607 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5181088331/10000000000 : ℝ)^4233 ≤ (21002066051557/50000000000000 : ℝ)^3209 := by
    have hnat : (5181088331 : ℕ)^4233*50000000000000^3209 ≤ 21002066051557^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181088331 10000000000 21002066051557 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34285261/62500000 : ℝ)^4233 ≤ (11322811307781/25000000000000 : ℝ)^3209 := by
    have hnat : (34285261 : ℕ)^4233*25000000000000^3209 ≤ 11322811307781^3209*62500000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34285261 62500000 11322811307781 25000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1046384549/5000000000 : ℝ), (5181088331/10000000000 : ℝ), (34285261/62500000 : ℝ)] ![(12704622657607/100000000000000 : ℝ), (21002066051557/50000000000000 : ℝ), (11322811307781/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1046384549/5000000000 : ℝ)|^4233 ≤ (12704622657607/100000000000000 : ℝ)^3209
        have hw : |(-1046384549/5000000000 : ℝ)|=(1046384549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5181088331/10000000000 : ℝ)|^4233 ≤ (21002066051557/50000000000000 : ℝ)^3209
        have hw : |(5181088331/10000000000 : ℝ)|=(5181088331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(34285261/62500000 : ℝ)|^4233 ≤ (11322811307781/25000000000000 : ℝ)^3209
        have hw : |(34285261/62500000 : ℝ)|=(34285261/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s2_5 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661189847/1250000000 : ℝ)*x 0 + (-486452449/2500000000 : ℝ)*x 1 + (27428209/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661189847/1250000000 : ℝ)^4233 ≤ (43167566087439/100000000000000 : ℝ)^3209 := by
    have hnat : (661189847 : ℕ)^4233*100000000000000^3209 ≤ 43167566087439^3209*1250000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661189847 1250000000 43167566087439 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (486452449/2500000000 : ℝ)^4233 ≤ (11541188227173/100000000000000 : ℝ)^3209 := by
    have hnat : (486452449 : ℕ)^4233*100000000000000^3209 ≤ 11541188227173^3209*2500000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486452449 2500000000 11541188227173 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27428209/50000000 : ℝ)^4233 ≤ (22645622833381/50000000000000 : ℝ)^3209 := by
    have hnat : (27428209 : ℕ)^4233*50000000000000^3209 ≤ 22645622833381^3209*50000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27428209 50000000 22645622833381 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661189847/1250000000 : ℝ), (-486452449/2500000000 : ℝ), (27428209/50000000 : ℝ)] ![(43167566087439/100000000000000 : ℝ), (11541188227173/100000000000000 : ℝ), (22645622833381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661189847/1250000000 : ℝ)|^4233 ≤ (43167566087439/100000000000000 : ℝ)^3209
        have hw : |(661189847/1250000000 : ℝ)|=(661189847/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-486452449/2500000000 : ℝ)|^4233 ≤ (11541188227173/100000000000000 : ℝ)^3209
        have hw : |(-486452449/2500000000 : ℝ)|=(486452449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(27428209/50000000 : ℝ)|^4233 ≤ (22645622833381/50000000000000 : ℝ)^3209
        have hw : |(27428209/50000000 : ℝ)|=(27428209/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s2_6 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661189859/1250000000 : ℝ)*x 0 + (219425677/400000000 : ℝ)*x 1 + (-1945809491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661189859/1250000000 : ℝ)^4233 ≤ (43167567120893/100000000000000 : ℝ)^3209 := by
    have hnat : (661189859 : ℕ)^4233*100000000000000^3209 ≤ 43167567120893^3209*1250000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661189859 1250000000 43167567120893 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (219425677/400000000 : ℝ)^4233 ≤ (45291247028129/100000000000000 : ℝ)^3209 := by
    have hnat : (219425677 : ℕ)^4233*100000000000000^3209 ≤ 45291247028129^3209*400000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219425677 400000000 45291247028129 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1945809491/10000000000 : ℝ)^4233 ≤ (5770592920427/50000000000000 : ℝ)^3209 := by
    have hnat : (1945809491 : ℕ)^4233*50000000000000^3209 ≤ 5770592920427^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1945809491 10000000000 5770592920427 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661189859/1250000000 : ℝ), (219425677/400000000 : ℝ), (-1945809491/10000000000 : ℝ)] ![(43167567120893/100000000000000 : ℝ), (45291247028129/100000000000000 : ℝ), (5770592920427/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661189859/1250000000 : ℝ)|^4233 ≤ (43167567120893/100000000000000 : ℝ)^3209
        have hw : |(661189859/1250000000 : ℝ)|=(661189859/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(219425677/400000000 : ℝ)|^4233 ≤ (45291247028129/100000000000000 : ℝ)^3209
        have hw : |(219425677/400000000 : ℝ)|=(219425677/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1945809491/10000000000 : ℝ)|^4233 ≤ (5770592920427/50000000000000 : ℝ)^3209
        have hw : |(-1945809491/10000000000 : ℝ)|=(1945809491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s2_7 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2169245789/5000000000 : ℝ)*x 0 + (932019653/2000000000 : ℝ)*x 1 + (4038589213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2169245789/5000000000 : ℝ)^4233 ≤ (8309074442201/25000000000000 : ℝ)^3209 := by
    have hnat : (2169245789 : ℕ)^4233*25000000000000^3209 ≤ 8309074442201^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169245789 5000000000 8309074442201 25000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (932019653/2000000000 : ℝ)^4233 ≤ (36524064897421/100000000000000 : ℝ)^3209 := by
    have hnat : (932019653 : ℕ)^4233*100000000000000^3209 ≤ 36524064897421^3209*2000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      932019653 2000000000 36524064897421 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4038589213/10000000000 : ℝ)^4233 ≤ (15119818662361/50000000000000 : ℝ)^3209 := by
    have hnat : (4038589213 : ℕ)^4233*50000000000000^3209 ≤ 15119818662361^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4038589213 10000000000 15119818662361 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2169245789/5000000000 : ℝ), (932019653/2000000000 : ℝ), (4038589213/10000000000 : ℝ)] ![(8309074442201/25000000000000 : ℝ), (36524064897421/100000000000000 : ℝ), (15119818662361/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2169245789/5000000000 : ℝ)|^4233 ≤ (8309074442201/25000000000000 : ℝ)^3209
        have hw : |(2169245789/5000000000 : ℝ)|=(2169245789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(932019653/2000000000 : ℝ)|^4233 ≤ (36524064897421/100000000000000 : ℝ)^3209
        have hw : |(932019653/2000000000 : ℝ)|=(932019653/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4038589213/10000000000 : ℝ)|^4233 ≤ (15119818662361/50000000000000 : ℝ)^3209
        have hw : |(4038589213/10000000000 : ℝ)|=(4038589213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1272_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38008999/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19869/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (397/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (9623/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1009/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19869/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (397/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19869/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (397/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19869/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (397/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19869/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (397/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19869/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (397/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19869/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (397/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (397/6250 : ℝ) ^ (8465/2048 : ℝ) ≤ (1127376533530067/100000000000000000000 : ℝ) := by
    have hpowers : (397/6250 : ℝ)^8465 ≤ (1127376533530067/100000000000000000000 : ℝ)^2048 := by
      have hnat : (397 : ℕ)^8465*100000000000000000000^2048 ≤ 1127376533530067^2048*6250^8465 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        397 6250 1127376533530067 100000000000000000000 8465 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (397/6250 : ℝ)) (X := (1127376533530067/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (19869/100000 : ℝ) ^ (8465/2048 : ℝ) ≤ (251292975378017/200000000000000000 : ℝ) := by
    have hpowers : (19869/100000 : ℝ)^8465 ≤ (251292975378017/200000000000000000 : ℝ)^2048 := by
      have hnat : (19869 : ℕ)^8465*200000000000000000^2048 ≤ 251292975378017^2048*100000^8465 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19869 100000 251292975378017 200000000000000000 8465 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19869/100000 : ℝ)) (X := (251292975378017/200000000000000000 : ℝ)) (by norm_num) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001127376533530067/50000000000000000000 : ℝ) ≤ (10000054550440847/10000000000000000 : ℝ) ^ (8465/2048 : ℝ) := by
    have hpowers : (50001127376533530067/50000000000000000000 : ℝ)^2048 ≤ (10000054550440847/10000000000000000 : ℝ)^8465 := by
      have hnat : (50001127376533530067 : ℕ)^2048*10000000000000000^8465 ≤ 10000054550440847^8465*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001127376533530067 50000000000000000000 10000054550440847 10000000000000000 2048 8465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000054550440847/10000000000000000 : ℝ)) (X := (50001127376533530067/50000000000000000000 : ℝ)) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100126773864222538567/100000000000000000000 : ℝ) ≤ (10003065661070947/10000000000000000 : ℝ) ^ (8465/2048 : ℝ) := by
    have hpowers : (100126773864222538567/100000000000000000000 : ℝ)^2048 ≤ (10003065661070947/10000000000000000 : ℝ)^8465 := by
      have hnat : (100126773864222538567 : ℕ)^2048*10000000000000000^8465 ≤ 10003065661070947^8465*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100126773864222538567 100000000000000000000 10003065661070947 10000000000000000 2048 8465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003065661070947/10000000000000000 : ℝ)) (X := (100126773864222538567/100000000000000000000 : ℝ)) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (100251292975378017/100000000000000000 : ℝ) ≤ (10006076771701047/10000000000000000 : ℝ) ^ (8465/2048 : ℝ) := by
    have hpowers : (100251292975378017/100000000000000000 : ℝ)^2048 ≤ (10006076771701047/10000000000000000 : ℝ)^8465 := by
      have hnat : (100251292975378017 : ℕ)^2048*10000000000000000^8465 ≤ 10006076771701047^8465*100000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100251292975378017 100000000000000000 10006076771701047 10000000000000000 2048 8465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006076771701047/10000000000000000 : ℝ)) (X := (100251292975378017/100000000000000000 : ℝ)) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1127376533530067/100000000000000000000 : ℝ) ≤ ((135132484208864138499/135170000000000000000 : ℝ)+2*(30111106301/13517000000000 : ℝ)*(397/6250 : ℝ))^(8465/2048 : ℝ) := by
    rw [show (135132484208864138499/135170000000000000000 : ℝ)+2*(30111106301/13517000000000 : ℝ)*(397/6250 : ℝ)=(10000054550440847/10000000000000000 : ℝ) by norm_num, show 1+2*(1127376533530067/100000000000000000000 : ℝ)=(50001127376533530067/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(251292975378017/200000000000000000 : ℝ)+(1127376533530067/100000000000000000000 : ℝ) ≤ ((135132484208864138499/135170000000000000000 : ℝ)+(30111106301/13517000000000 : ℝ)*((19869/100000 : ℝ)+(397/6250 : ℝ)))^(8465/2048 : ℝ) := by
    rw [show (135132484208864138499/135170000000000000000 : ℝ)+(30111106301/13517000000000 : ℝ)*((19869/100000 : ℝ)+(397/6250 : ℝ))=(10003065661070947/10000000000000000 : ℝ) by norm_num, show 1+(251292975378017/200000000000000000 : ℝ)+(1127376533530067/100000000000000000000 : ℝ)=(100126773864222538567/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(251292975378017/200000000000000000 : ℝ) ≤ ((135132484208864138499/135170000000000000000 : ℝ)+2*(30111106301/13517000000000 : ℝ)*(19869/100000 : ℝ))^(8465/2048 : ℝ) := by
    rw [show (135132484208864138499/135170000000000000000 : ℝ)+2*(30111106301/13517000000000 : ℝ)*(19869/100000 : ℝ)=(10006076771701047/10000000000000000 : ℝ) by norm_num, show 1+2*(251292975378017/200000000000000000 : ℝ)=(100251292975378017/100000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (135132484208864138499/135170000000000000000 : ℝ)*(X 1 0+X 2 0)+(30111106301/13517000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8465/2048 : ℝ)) (lo := (397/6250 : ℝ)) (hi := (19869/100000 : ℝ)) (c := (135132484208864138499/135170000000000000000 : ℝ)) (alpha := (30111106301/13517000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (135132484208864138499/135170000000000000000 : ℝ)*(X 0 1+X 2 1)+(30111106301/13517000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8465/2048 : ℝ)) (lo := (397/6250 : ℝ)) (hi := (19869/100000 : ℝ)) (c := (135132484208864138499/135170000000000000000 : ℝ)) (alpha := (30111106301/13517000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (135132484208864138499/135170000000000000000 : ℝ)*(X 0 2+X 1 2)+(30111106301/13517000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8465/2048 : ℝ)) (lo := (397/6250 : ℝ)) (hi := (19869/100000 : ℝ)) (c := (135132484208864138499/135170000000000000000 : ℝ)) (alpha := (30111106301/13517000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2092696897/10000000000 : ℝ)*X 0 0+(5487600583/10000000000 : ℝ)*X 0 1+(5179147311/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2684219891/5000000000 : ℝ)*X 1 0+(-450460849/2000000000 : ℝ)*X 1 1+(1035829521/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((671054969/1250000000 : ℝ)*X 2 0+(2589573787/5000000000 : ℝ)*X 2 1+(-90092173/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1084586149/2500000000 : ℝ)*X 0 0+(1008648207/2500000000 : ℝ)*X 0 1+(4664058739/10000000000 : ℝ)*X 0 2+(1084586149/2500000000 : ℝ)*X 1 0+(1008648207/2500000000 : ℝ)*X 1 1+(4664058739/10000000000 : ℝ)*X 1 2+(1084586149/2500000000 : ℝ)*X 2 0+(1008648207/2500000000 : ℝ)*X 2 1+(4664058739/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1046384549/5000000000 : ℝ)*X 0 0+(5181088331/10000000000 : ℝ)*X 0 1+(34285261/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((661189847/1250000000 : ℝ)*X 1 0+(-486452449/2500000000 : ℝ)*X 1 1+(27428209/50000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((661189859/1250000000 : ℝ)*X 2 0+(219425677/400000000 : ℝ)*X 2 1+(-1945809491/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2169245789/5000000000 : ℝ)*X 0 0+(932019653/2000000000 : ℝ)*X 0 1+(4038589213/10000000000 : ℝ)*X 0 2+(2169245789/5000000000 : ℝ)*X 1 0+(932019653/2000000000 : ℝ)*X 1 1+(4038589213/10000000000 : ℝ)*X 1 2+(2169245789/5000000000 : ℝ)*X 2 0+(932019653/2000000000 : ℝ)*X 2 1+(4038589213/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (105215400421340032133607/13517000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1385313013/100000000000000 : ℝ)*(base19) + (164114483/12500000000000 : ℝ)*(base23) + (14569959/50000000000000 : ℝ)*(lower2) + (42194551/20000000000000 : ℝ)*(upper3) + (10446831/10000000000000 : ℝ)*(upper5) + (1207671287439527/50000000000000 : ℝ)*(major0) + (1207671287439527/50000000000000 : ℝ)*(major1) + (1207671287439527/50000000000000 : ℝ)*(major2) + (324200192751493/10000000000000 : ℝ)*(sp0) + (3242018558240693/100000000000000 : ℝ)*(sp1) + (1621009315318921/50000000000000 : ℝ)*(sp2) + (158865609716561/10000000000000 : ℝ)*(sp3) + (18016038777/100000000000000 : ℝ)*(sp4) + (8849574407/100000000000000 : ℝ)*(sp7) + (1588664946740017/100000000000000 : ℝ)*(f.failure) + (1621009971776853/50000000000000 : ℝ)*(f.sum) + (3221235403157/1351700000000000000000000000 : ℝ)*base66 + (16912664150033049973/6758500000000000000000000000000000 : ℝ)*base67 + (52837447811528450027/6758500000000000000000000000000000 : ℝ)*base70 + (28315031450536950027/6758500000000000000000000000000000 : ℝ)*base72 + (5158216883853/1351700000000000000000000000 : ℝ)*base73 + (37374270031344049973/6758500000000000000000000000000000 : ℝ)*base75 + (441938385229950027/6758500000000000000000000000000000 : ℝ)*base78 + (87880429036369549973/6758500000000000000000000000000000 : ℝ)*base79 + (62621121537547/13517000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (9412983/2500000000000000000000 : ℝ)*base89 + (9412983/2500000000000000000000 : ℝ)*base91 + (9412983/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (50975998034763436002267/6758500000000000000000000000 : ℝ) := by norm_num
    linear_combination (190281711/10000000000000 : ℝ)*(base19) + (2106844159/100000000000000 : ℝ)*(base23) + (30790853/100000000000000 : ℝ)*(upper2) + (253836957/100000000000000 : ℝ)*(upper3) + (72401329/50000000000000 : ℝ)*(upper5) + (1223120601433013/50000000000000 : ℝ)*(major0) + (1223120601433013/50000000000000 : ℝ)*(major1) + (1223120601433013/50000000000000 : ℝ)*(major2) + (4034639679/20000000000000 : ℝ)*(sp1) + (6488049397/25000000000000 : ℝ)*(sp2) + (1641746987854617/50000000000000 : ℝ)*(sp4) + (3283471899693729/100000000000000 : ℝ)*(sp5) + (1641732958333743/50000000000000 : ℝ)*(sp6) + (1608988178606089/100000000000000 : ℝ)*(sp7) + (1608988178606089/100000000000000 : ℝ)*(f.failure) + (1641746987854617/50000000000000 : ℝ)*(f.sum) + (865174171277/270340000000000000000000000 : ℝ)*base65 + (12125692923348632513/6758500000000000000000000000000000 : ℝ)*base68 + (5617763721208367487/6758500000000000000000000000000000 : ℝ)*base69 + (8698052043073132513/6758500000000000000000000000000000 : ℝ)*base72 + (31523041221789/6758500000000000000000000000 : ℝ)*base73 + (62010182051889132513/6758500000000000000000000000000000 : ℝ)*base76 + (7306019361247867487/6758500000000000000000000000000000 : ℝ)*base77 + (17486988366983367487/6758500000000000000000000000000000 : ℝ)*base79 + (56815276594093/13517000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (8194911/2500000000000000000000 : ℝ)*base89 + (8194911/2500000000000000000000 : ℝ)*base91 + (8194911/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1272_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38008999/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19869/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (397/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9623/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1009/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1272_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1272_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38008999/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9623/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1009/6250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1272_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1272_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1272_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38008999/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9623/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1009/6250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1272_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

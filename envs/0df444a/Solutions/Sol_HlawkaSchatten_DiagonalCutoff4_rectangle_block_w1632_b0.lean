-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1632_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:00:04.651616+00:00
-- url     : https://prove2.me/submissions/676f9c1d-0b6c-49c1-89fe-a06ddb2eab56

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
theorem support_rectangle_w1632_s0_0 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-190596747/1250000000 : ℝ)*x 0 + (5808048603/10000000000 : ℝ)*x 1 + (2454528997/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (190596747/1250000000 : ℝ)^4847 ≤ (9213508428343/100000000000000 : ℝ)^3823 := by
    have hnat : (190596747 : ℕ)^4847*100000000000000^3823 ≤ 9213508428343^3823*1250000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190596747 1250000000 9213508428343 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5808048603/10000000000 : ℝ)^4847 ≤ (50214039399267/100000000000000 : ℝ)^3823 := by
    have hnat : (5808048603 : ℕ)^4847*100000000000000^3823 ≤ 50214039399267^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5808048603 10000000000 50214039399267 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2454528997/5000000000 : ℝ)^4847 ≤ (20286226079023/50000000000000 : ℝ)^3823 := by
    have hnat : (2454528997 : ℕ)^4847*50000000000000^3823 ≤ 20286226079023^3823*5000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2454528997 5000000000 20286226079023 50000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-190596747/1250000000 : ℝ), (5808048603/10000000000 : ℝ), (2454528997/5000000000 : ℝ)] ![(9213508428343/100000000000000 : ℝ), (50214039399267/100000000000000 : ℝ), (20286226079023/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-190596747/1250000000 : ℝ)|^4847 ≤ (9213508428343/100000000000000 : ℝ)^3823
        have hw : |(-190596747/1250000000 : ℝ)|=(190596747/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5808048603/10000000000 : ℝ)|^4847 ≤ (50214039399267/100000000000000 : ℝ)^3823
        have hw : |(5808048603/10000000000 : ℝ)|=(5808048603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2454528997/5000000000 : ℝ)|^4847 ≤ (20286226079023/50000000000000 : ℝ)^3823
        have hw : |(2454528997/5000000000 : ℝ)|=(2454528997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s0_1 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (544473971/1000000000 : ℝ)*x 0 + (-2020119171/10000000000 : ℝ)*x 1 + (490905963/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544473971/1000000000 : ℝ)^4847 ≤ (23132786352543/50000000000000 : ℝ)^3823 := by
    have hnat : (544473971 : ℕ)^4847*50000000000000^3823 ≤ 23132786352543^3823*1000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544473971 1000000000 23132786352543 50000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2020119171/10000000000 : ℝ)^4847 ≤ (6580978989171/50000000000000 : ℝ)^3823 := by
    have hnat : (2020119171 : ℕ)^4847*50000000000000^3823 ≤ 6580978989171^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2020119171 10000000000 6580978989171 50000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (490905963/1000000000 : ℝ)^4847 ≤ (2028623465049/5000000000000 : ℝ)^3823 := by
    have hnat : (490905963 : ℕ)^4847*5000000000000^3823 ≤ 2028623465049^3823*1000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490905963 1000000000 2028623465049 5000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544473971/1000000000 : ℝ), (-2020119171/10000000000 : ℝ), (490905963/1000000000 : ℝ)] ![(23132786352543/50000000000000 : ℝ), (6580978989171/50000000000000 : ℝ), (2028623465049/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544473971/1000000000 : ℝ)|^4847 ≤ (23132786352543/50000000000000 : ℝ)^3823
        have hw : |(544473971/1000000000 : ℝ)|=(544473971/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2020119171/10000000000 : ℝ)|^4847 ≤ (6580978989171/50000000000000 : ℝ)^3823
        have hw : |(-2020119171/10000000000 : ℝ)|=(2020119171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(490905963/1000000000 : ℝ)|^4847 ≤ (2028623465049/5000000000000 : ℝ)^3823
        have hw : |(490905963/1000000000 : ℝ)|=(490905963/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s0_2 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5444740393/10000000000 : ℝ)*x 0 + (306816151/625000000 : ℝ)*x 1 + (-2020119821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5444740393/10000000000 : ℝ)^4847 ≤ (1445799376977/3125000000000 : ℝ)^3823 := by
    have hnat : (5444740393 : ℕ)^4847*3125000000000^3823 ≤ 1445799376977^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5444740393 10000000000 1445799376977 3125000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (306816151/625000000 : ℝ)^4847 ≤ (40572456580001/100000000000000 : ℝ)^3823 := by
    have hnat : (306816151 : ℕ)^4847*100000000000000^3823 ≤ 40572456580001^3823*625000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      306816151 625000000 40572456580001 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2020119821/10000000000 : ℝ)^4847 ≤ (658098167387/5000000000000 : ℝ)^3823 := by
    have hnat : (2020119821 : ℕ)^4847*5000000000000^3823 ≤ 658098167387^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2020119821 10000000000 658098167387 5000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5444740393/10000000000 : ℝ), (306816151/625000000 : ℝ), (-2020119821/10000000000 : ℝ)] ![(1445799376977/3125000000000 : ℝ), (40572456580001/100000000000000 : ℝ), (658098167387/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5444740393/10000000000 : ℝ)|^4847 ≤ (1445799376977/3125000000000 : ℝ)^3823
        have hw : |(5444740393/10000000000 : ℝ)|=(5444740393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(306816151/625000000 : ℝ)|^4847 ≤ (40572456580001/100000000000000 : ℝ)^3823
        have hw : |(306816151/625000000 : ℝ)|=(306816151/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2020119821/10000000000 : ℝ)|^4847 ≤ (658098167387/5000000000000 : ℝ)^3823
        have hw : |(-2020119821/10000000000 : ℝ)|=(2020119821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s0_3 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4099127691/10000000000 : ℝ)*x 0 + (384805493/1250000000 : ℝ)*x 1 + (5351698903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4099127691/10000000000 : ℝ)^4847 ≤ (16140608300649/50000000000000 : ℝ)^3823 := by
    have hnat : (4099127691 : ℕ)^4847*50000000000000^3823 ≤ 16140608300649^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4099127691 10000000000 16140608300649 50000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (384805493/1250000000 : ℝ)^4847 ≤ (22453265427627/100000000000000 : ℝ)^3823 := by
    have hnat : (384805493 : ℕ)^4847*100000000000000^3823 ≤ 22453265427627^3823*1250000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      384805493 1250000000 22453265427627 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5351698903/10000000000 : ℝ)^4847 ≤ (45265517954601/100000000000000 : ℝ)^3823 := by
    have hnat : (5351698903 : ℕ)^4847*100000000000000^3823 ≤ 45265517954601^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351698903 10000000000 45265517954601 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4099127691/10000000000 : ℝ), (384805493/1250000000 : ℝ), (5351698903/10000000000 : ℝ)] ![(16140608300649/50000000000000 : ℝ), (22453265427627/100000000000000 : ℝ), (45265517954601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4099127691/10000000000 : ℝ)|^4847 ≤ (16140608300649/50000000000000 : ℝ)^3823
        have hw : |(4099127691/10000000000 : ℝ)|=(4099127691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(384805493/1250000000 : ℝ)|^4847 ≤ (22453265427627/100000000000000 : ℝ)^3823
        have hw : |(384805493/1250000000 : ℝ)|=(384805493/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5351698903/10000000000 : ℝ)|^4847 ≤ (45265517954601/100000000000000 : ℝ)^3823
        have hw : |(5351698903/10000000000 : ℝ)|=(5351698903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s0_4 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-763641291/5000000000 : ℝ)*x 0 + (4931570099/10000000000 : ℝ)*x 1 + (1156949717/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (763641291/5000000000 : ℝ)^4847 ≤ (4616365608433/50000000000000 : ℝ)^3823 := by
    have hnat : (763641291 : ℕ)^4847*50000000000000^3823 ≤ 4616365608433^3823*5000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      763641291 5000000000 4616365608433 50000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4931570099/10000000000 : ℝ)^4847 ≤ (816169828633/2000000000000 : ℝ)^3823 := by
    have hnat : (4931570099 : ℕ)^4847*2000000000000^3823 ≤ 816169828633^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4931570099 10000000000 816169828633 2000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1156949717/2000000000 : ℝ)^4847 ≤ (24979388669353/50000000000000 : ℝ)^3823 := by
    have hnat : (1156949717 : ℕ)^4847*50000000000000^3823 ≤ 24979388669353^3823*2000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1156949717 2000000000 24979388669353 50000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-763641291/5000000000 : ℝ), (4931570099/10000000000 : ℝ), (1156949717/2000000000 : ℝ)] ![(4616365608433/50000000000000 : ℝ), (816169828633/2000000000000 : ℝ), (24979388669353/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-763641291/5000000000 : ℝ)|^4847 ≤ (4616365608433/50000000000000 : ℝ)^3823
        have hw : |(-763641291/5000000000 : ℝ)|=(763641291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4931570099/10000000000 : ℝ)|^4847 ≤ (816169828633/2000000000000 : ℝ)^3823
        have hw : |(4931570099/10000000000 : ℝ)|=(4931570099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1156949717/2000000000 : ℝ)|^4847 ≤ (24979388669353/50000000000000 : ℝ)^3823
        have hw : |(1156949717/2000000000 : ℝ)|=(1156949717/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s0_5 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5199302377/10000000000 : ℝ)*x 0 + (-114442913/1000000000 : ℝ)*x 1 + (2892374409/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5199302377/10000000000 : ℝ)^4847 ≤ (43637540195533/100000000000000 : ℝ)^3823 := by
    have hnat : (5199302377 : ℕ)^4847*100000000000000^3823 ≤ 43637540195533^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5199302377 10000000000 43637540195533 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (114442913/1000000000 : ℝ)^4847 ≤ (6403679895989/100000000000000 : ℝ)^3823 := by
    have hnat : (114442913 : ℕ)^4847*100000000000000^3823 ≤ 6403679895989^3823*1000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114442913 1000000000 6403679895989 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2892374409/5000000000 : ℝ)^4847 ≤ (49958779889949/100000000000000 : ℝ)^3823 := by
    have hnat : (2892374409 : ℕ)^4847*100000000000000^3823 ≤ 49958779889949^3823*5000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2892374409 5000000000 49958779889949 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5199302377/10000000000 : ℝ), (-114442913/1000000000 : ℝ), (2892374409/5000000000 : ℝ)] ![(43637540195533/100000000000000 : ℝ), (6403679895989/100000000000000 : ℝ), (49958779889949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5199302377/10000000000 : ℝ)|^4847 ≤ (43637540195533/100000000000000 : ℝ)^3823
        have hw : |(5199302377/10000000000 : ℝ)|=(5199302377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-114442913/1000000000 : ℝ)|^4847 ≤ (6403679895989/100000000000000 : ℝ)^3823
        have hw : |(-114442913/1000000000 : ℝ)|=(114442913/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2892374409/5000000000 : ℝ)|^4847 ≤ (49958779889949/100000000000000 : ℝ)^3823
        have hw : |(2892374409/5000000000 : ℝ)|=(2892374409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s0_6 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5199302431/10000000000 : ℝ)*x 0 + (5784748609/10000000000 : ℝ)*x 1 + (-1144429371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5199302431/10000000000 : ℝ)^4847 ≤ (10909385192537/25000000000000 : ℝ)^3823 := by
    have hnat : (5199302431 : ℕ)^4847*25000000000000^3823 ≤ 10909385192537^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5199302431 10000000000 10909385192537 25000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5784748609/10000000000 : ℝ)^4847 ≤ (9991755520299/20000000000000 : ℝ)^3823 := by
    have hnat : (5784748609 : ℕ)^4847*20000000000000^3823 ≤ 9991755520299^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5784748609 10000000000 9991755520299 20000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1144429371/10000000000 : ℝ)^4847 ≤ (1280736321143/20000000000000 : ℝ)^3823 := by
    have hnat : (1144429371 : ℕ)^4847*20000000000000^3823 ≤ 1280736321143^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1144429371 10000000000 1280736321143 20000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5199302431/10000000000 : ℝ), (5784748609/10000000000 : ℝ), (-1144429371/10000000000 : ℝ)] ![(10909385192537/25000000000000 : ℝ), (9991755520299/20000000000000 : ℝ), (1280736321143/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5199302431/10000000000 : ℝ)|^4847 ≤ (10909385192537/25000000000000 : ℝ)^3823
        have hw : |(5199302431/10000000000 : ℝ)|=(5199302431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5784748609/10000000000 : ℝ)|^4847 ≤ (9991755520299/20000000000000 : ℝ)^3823
        have hw : |(5784748609/10000000000 : ℝ)|=(5784748609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1144429371/10000000000 : ℝ)|^4847 ≤ (1280736321143/20000000000000 : ℝ)^3823
        have hw : |(-1144429371/10000000000 : ℝ)|=(1144429371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s0_7 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4105471947/10000000000 : ℝ)*x 0 + (165461673/312500000 : ℝ)*x 1 + (627472303/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4105471947/10000000000 : ℝ)^4847 ≤ (2021535879617/6250000000000 : ℝ)^3823 := by
    have hnat : (4105471947 : ℕ)^4847*6250000000000^3823 ≤ 2021535879617^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4105471947 10000000000 2021535879617 6250000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (165461673/312500000 : ℝ)^4847 ≤ (11163984860537/25000000000000 : ℝ)^3823 := by
    have hnat : (165461673 : ℕ)^4847*25000000000000^3823 ≤ 11163984860537^3823*312500000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165461673 312500000 11163984860537 25000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (627472303/2000000000 : ℝ)^4847 ≤ (22999486465997/100000000000000 : ℝ)^3823 := by
    have hnat : (627472303 : ℕ)^4847*100000000000000^3823 ≤ 22999486465997^3823*2000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627472303 2000000000 22999486465997 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4105471947/10000000000 : ℝ), (165461673/312500000 : ℝ), (627472303/2000000000 : ℝ)] ![(2021535879617/6250000000000 : ℝ), (11163984860537/25000000000000 : ℝ), (22999486465997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4105471947/10000000000 : ℝ)|^4847 ≤ (2021535879617/6250000000000 : ℝ)^3823
        have hw : |(4105471947/10000000000 : ℝ)|=(4105471947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(165461673/312500000 : ℝ)|^4847 ≤ (11163984860537/25000000000000 : ℝ)^3823
        have hw : |(165461673/312500000 : ℝ)|=(165461673/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(627472303/2000000000 : ℝ)|^4847 ≤ (22999486465997/100000000000000 : ℝ)^3823
        have hw : |(627472303/2000000000 : ℝ)|=(627472303/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1632_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (176433729/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2243/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (11873/50000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4843/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4843 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4843*1^1024 ≤ 0^1024*1^4843 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4843 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4843 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4843/1024 : ℝ) ≤ (1312036261017482473/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4843 ≤ (1312036261017482473/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4843*100000000000000000000^1024 ≤ 1312036261017482473^1024*5^4843 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1312036261017482473 100000000000000000000 4843 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1312036261017482473/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4843 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4843/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4843 := by
      have hnat : (1 : ℕ)^1024*1^4843 ≤ 1^4843*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4843 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4843 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101312036261017482473/100000000000000000000 : ℝ) ≤ (10027599190837091/10000000000000000 : ℝ) ^ (4843/1024 : ℝ) := by
    have hpowers : (101312036261017482473/100000000000000000000 : ℝ)^1024 ≤ (10027599190837091/10000000000000000 : ℝ)^4843 := by
      have hnat : (101312036261017482473 : ℕ)^1024*10000000000000000^4843 ≤ 10027599190837091^4843*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101312036261017482473 100000000000000000000 10027599190837091 10000000000000000 1024 4843 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10027599190837091/10000000000000000 : ℝ)) (X := (101312036261017482473/100000000000000000000 : ℝ)) (by norm_num) 4843 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51312036261017482473/50000000000000000000 : ℝ) ≤ (5027599190837091/5000000000000000 : ℝ) ^ (4843/1024 : ℝ) := by
    have hpowers : (51312036261017482473/50000000000000000000 : ℝ)^1024 ≤ (5027599190837091/5000000000000000 : ℝ)^4843 := by
      have hnat : (51312036261017482473 : ℕ)^1024*5000000000000000^4843 ≤ 5027599190837091^4843*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51312036261017482473 50000000000000000000 5027599190837091 5000000000000000 1024 4843 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5027599190837091/5000000000000000 : ℝ)) (X := (51312036261017482473/50000000000000000000 : ℝ)) (by norm_num) 4843 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(27599190837091/4000000000000000 : ℝ)*(0 : ℝ))^(4843/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(27599190837091/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1312036261017482473/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(27599190837091/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4843/1024 : ℝ) := by
    rw [show (1 : ℝ)+(27599190837091/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10027599190837091/10000000000000000 : ℝ) by norm_num, show 1+(1312036261017482473/100000000000000000000 : ℝ)+(0 : ℝ)=(101312036261017482473/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1312036261017482473/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(27599190837091/4000000000000000 : ℝ)*(2/5 : ℝ))^(4843/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(27599190837091/4000000000000000 : ℝ)*(2/5 : ℝ)=(5027599190837091/5000000000000000 : ℝ) by norm_num, show 1+2*(1312036261017482473/100000000000000000000 : ℝ)=(51312036261017482473/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(27599190837091/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4843/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27599190837091/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(27599190837091/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4843/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27599190837091/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(27599190837091/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4843/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27599190837091/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-190596747/1250000000 : ℝ)*X 0 0+(5808048603/10000000000 : ℝ)*X 0 1+(2454528997/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((544473971/1000000000 : ℝ)*X 1 0+(-2020119171/10000000000 : ℝ)*X 1 1+(490905963/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5444740393/10000000000 : ℝ)*X 2 0+(306816151/625000000 : ℝ)*X 2 1+(-2020119821/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4099127691/10000000000 : ℝ)*X 0 0+(384805493/1250000000 : ℝ)*X 0 1+(5351698903/10000000000 : ℝ)*X 0 2+(4099127691/10000000000 : ℝ)*X 1 0+(384805493/1250000000 : ℝ)*X 1 1+(5351698903/10000000000 : ℝ)*X 1 2+(4099127691/10000000000 : ℝ)*X 2 0+(384805493/1250000000 : ℝ)*X 2 1+(5351698903/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-763641291/5000000000 : ℝ)*X 0 0+(4931570099/10000000000 : ℝ)*X 0 1+(1156949717/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5199302377/10000000000 : ℝ)*X 1 0+(-114442913/1000000000 : ℝ)*X 1 1+(2892374409/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5199302431/10000000000 : ℝ)*X 2 0+(5784748609/10000000000 : ℝ)*X 2 1+(-1144429371/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4105471947/10000000000 : ℝ)*X 0 0+(165461673/312500000 : ℝ)*X 0 1+(627472303/2000000000 : ℝ)*X 0 2+(4105471947/10000000000 : ℝ)*X 1 0+(165461673/312500000 : ℝ)*X 1 1+(627472303/2000000000 : ℝ)*X 1 2+(4105471947/10000000000 : ℝ)*X 2 0+(165461673/312500000 : ℝ)*X 2 1+(627472303/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (131160118910900496375609/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (116663159/10000000000000 : ℝ)*(base19) + (647311477/50000000000000 : ℝ)*(base23) + (267788621/100000000000000 : ℝ)*(upper3) + (3143453/50000000000000 : ℝ)*(upper4) + (3123839/4000000000000 : ℝ)*(upper5) + (77613726613233/10000000000000 : ℝ)*(major0) + (77613726613233/10000000000000 : ℝ)*(major1) + (77613726613233/10000000000000 : ℝ)*(major2) + (1112365511577909/100000000000000 : ℝ)*(sp0) + (556185073729131/50000000000000 : ℝ)*(sp1) + (1112370019466897/100000000000000 : ℝ)*(sp2) + (17596001646799/4000000000000 : ℝ)*(sp3) + (2901255971/50000000000000 : ℝ)*(sp4) + (295840463/10000000000000 : ℝ)*(sp7) + (87980599914921/20000000000000 : ℝ)*(f.failure) + (1112371314089851/100000000000000 : ℝ)*(f.sum) + (72167629685203/20000000000000000000000000000 : ℝ)*base65 + (248613790774797/40000000000000000000000000000 : ℝ)*base68 + (119537328185203/40000000000000000000000000000 : ℝ)*base69 + (197061386374797/40000000000000000000000000000 : ℝ)*base72 + (12468577734797/20000000000000000000000000000 : ℝ)*base74 + (337814929574797/40000000000000000000000000000 : ℝ)*base76 + (26792846414797/40000000000000000000000000000 : ℝ)*base78 + (152634661454797/40000000000000000000000000000 : ℝ)*base80 + (75689939065203/20000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (5229591/2000000000000000000000 : ℝ)*base90 + (5229591/2000000000000000000000 : ℝ)*base92 + (5229591/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (116489626185415969872909/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (544248317/100000000000000 : ℝ)*(base19) + (22101837/4000000000000 : ℝ)*(base23) + (2165873/12500000000000 : ℝ)*(base32) + (3820167/5000000000000 : ℝ)*(upper3) + (3975049/20000000000000 : ℝ)*(upper5) + (817802846953333/100000000000000 : ℝ)*(major0) + (817802846953333/100000000000000 : ℝ)*(major1) + (817802846953333/100000000000000 : ℝ)*(major2) + (514796317/25000000000000 : ℝ)*(sp1) + (988539079/50000000000000 : ℝ)*(sp2) + (586043594171417/50000000000000 : ℝ)*(sp4) + (1172084584909249/100000000000000 : ℝ)*(sp5) + (36627645584961/3125000000000 : ℝ)*(sp6) + (46351841057709/10000000000000 : ℝ)*(sp7) + (231759213952037/50000000000000 : ℝ)*(f.failure) + (586043594171417/50000000000000 : ℝ)*(f.sum) + (91076085925697/200000000000000000000000000000 : ℝ)*base66 + (2692525039925697/400000000000000000000000000000 : ℝ)*base68 + (2071673213525697/400000000000000000000000000000 : ℝ)*base70 + (1301429270725697/400000000000000000000000000000 : ℝ)*base72 + (464499525925697/200000000000000000000000000000 : ℝ)*base74 + (2528936666325697/400000000000000000000000000000 : ℝ)*base76 + (2908607291925697/400000000000000000000000000000 : ℝ)*base78 + (6475954291925697/400000000000000000000000000000 : ℝ)*base80 + (272067954474303/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (65055973/5000000000000000000000 : ℝ)*base89 + (65055973/5000000000000000000000 : ℝ)*base91 + (65055973/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1632_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (176433729/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2243/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (11873/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1632_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1632_s1_0 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-819145683/5000000000 : ℝ)*x 0 + (5510478247/10000000000 : ℝ)*x 1 + (2566507121/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (819145683/5000000000 : ℝ)^4847 ≤ (10091689228819/100000000000000 : ℝ)^3823 := by
    have hnat : (819145683 : ℕ)^4847*100000000000000^3823 ≤ 10091689228819^3823*5000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      819145683 5000000000 10091689228819 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5510478247/10000000000 : ℝ)^4847 ≤ (5871867100637/12500000000000 : ℝ)^3823 := by
    have hnat : (5510478247 : ℕ)^4847*12500000000000^3823 ≤ 5871867100637^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510478247 10000000000 5871867100637 12500000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2566507121/5000000000 : ℝ)^4847 ≤ (42933373955019/100000000000000 : ℝ)^3823 := by
    have hnat : (2566507121 : ℕ)^4847*100000000000000^3823 ≤ 42933373955019^3823*5000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2566507121 5000000000 42933373955019 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-819145683/5000000000 : ℝ), (5510478247/10000000000 : ℝ), (2566507121/5000000000 : ℝ)] ![(10091689228819/100000000000000 : ℝ), (5871867100637/12500000000000 : ℝ), (42933373955019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-819145683/5000000000 : ℝ)|^4847 ≤ (10091689228819/100000000000000 : ℝ)^3823
        have hw : |(-819145683/5000000000 : ℝ)|=(819145683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5510478247/10000000000 : ℝ)|^4847 ≤ (5871867100637/12500000000000 : ℝ)^3823
        have hw : |(5510478247/10000000000 : ℝ)|=(5510478247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2566507121/5000000000 : ℝ)|^4847 ≤ (42933373955019/100000000000000 : ℝ)^3823
        have hw : |(2566507121/5000000000 : ℝ)|=(2566507121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s1_1 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1073117819/2000000000 : ℝ)*x 0 + (-91750867/500000000 : ℝ)*x 1 + (2566507007/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073117819/2000000000 : ℝ)^4847 ≤ (45414523912427/100000000000000 : ℝ)^3823 := by
    have hnat : (1073117819 : ℕ)^4847*100000000000000^3823 ≤ 45414523912427^3823*2000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073117819 2000000000 45414523912427 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (91750867/500000000 : ℝ)^4847 ≤ (2913026135767/25000000000000 : ℝ)^3823 := by
    have hnat : (91750867 : ℕ)^4847*25000000000000^3823 ≤ 2913026135767^3823*500000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91750867 500000000 2913026135767 25000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2566507007/5000000000 : ℝ)^4847 ≤ (42933371537187/100000000000000 : ℝ)^3823 := by
    have hnat : (2566507007 : ℕ)^4847*100000000000000^3823 ≤ 42933371537187^3823*5000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2566507007 5000000000 42933371537187 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073117819/2000000000 : ℝ), (-91750867/500000000 : ℝ), (2566507007/5000000000 : ℝ)] ![(45414523912427/100000000000000 : ℝ), (2913026135767/25000000000000 : ℝ), (42933371537187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073117819/2000000000 : ℝ)|^4847 ≤ (45414523912427/100000000000000 : ℝ)^3823
        have hw : |(1073117819/2000000000 : ℝ)|=(1073117819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-91750867/500000000 : ℝ)|^4847 ≤ (2913026135767/25000000000000 : ℝ)^3823
        have hw : |(-91750867/500000000 : ℝ)|=(91750867/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2566507007/5000000000 : ℝ)|^4847 ≤ (42933371537187/100000000000000 : ℝ)^3823
        have hw : |(2566507007/5000000000 : ℝ)|=(2566507007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s1_2 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1073117983/2000000000 : ℝ)*x 0 + (1026602603/2000000000 : ℝ)*x 1 + (-1835017561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073117983/2000000000 : ℝ)^4847 ≤ (45414532711967/100000000000000 : ℝ)^3823 := by
    have hnat : (1073117983 : ℕ)^4847*100000000000000^3823 ≤ 45414532711967^3823*2000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073117983 2000000000 45414532711967 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1026602603/2000000000 : ℝ)^4847 ≤ (8586672188653/20000000000000 : ℝ)^3823 := by
    have hnat : (1026602603 : ℕ)^4847*20000000000000^3823 ≤ 8586672188653^3823*2000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026602603 2000000000 8586672188653 20000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1835017561/10000000000 : ℝ)^4847 ≤ (1165210632227/10000000000000 : ℝ)^3823 := by
    have hnat : (1835017561 : ℕ)^4847*10000000000000^3823 ≤ 1165210632227^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1835017561 10000000000 1165210632227 10000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073117983/2000000000 : ℝ), (1026602603/2000000000 : ℝ), (-1835017561/10000000000 : ℝ)] ![(45414532711967/100000000000000 : ℝ), (8586672188653/20000000000000 : ℝ), (1165210632227/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073117983/2000000000 : ℝ)|^4847 ≤ (45414532711967/100000000000000 : ℝ)^3823
        have hw : |(1073117983/2000000000 : ℝ)|=(1073117983/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1026602603/2000000000 : ℝ)|^4847 ≤ (8586672188653/20000000000000 : ℝ)^3823
        have hw : |(1026602603/2000000000 : ℝ)|=(1026602603/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1835017561/10000000000 : ℝ)|^4847 ≤ (1165210632227/10000000000000 : ℝ)^3823
        have hw : |(-1835017561/10000000000 : ℝ)|=(1835017561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s1_3 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4185824723/10000000000 : ℝ)*x 0 + (3728792993/10000000000 : ℝ)*x 1 + (2341639257/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4185824723/10000000000 : ℝ)^4847 ≤ (3314928420429/10000000000000 : ℝ)^3823 := by
    have hnat : (4185824723 : ℕ)^4847*10000000000000^3823 ≤ 3314928420429^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4185824723 10000000000 3314928420429 10000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3728792993/10000000000 : ℝ)^4847 ≤ (1789335565719/6250000000000 : ℝ)^3823 := by
    have hnat : (3728792993 : ℕ)^4847*6250000000000^3823 ≤ 1789335565719^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3728792993 10000000000 1789335565719 6250000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2341639257/5000000000 : ℝ)^4847 ≤ (3822134673103/10000000000000 : ℝ)^3823 := by
    have hnat : (2341639257 : ℕ)^4847*10000000000000^3823 ≤ 3822134673103^3823*5000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2341639257 5000000000 3822134673103 10000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4185824723/10000000000 : ℝ), (3728792993/10000000000 : ℝ), (2341639257/5000000000 : ℝ)] ![(3314928420429/10000000000000 : ℝ), (1789335565719/6250000000000 : ℝ), (3822134673103/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4185824723/10000000000 : ℝ)|^4847 ≤ (3314928420429/10000000000000 : ℝ)^3823
        have hw : |(4185824723/10000000000 : ℝ)|=(4185824723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3728792993/10000000000 : ℝ)|^4847 ≤ (1789335565719/6250000000000 : ℝ)^3823
        have hw : |(3728792993/10000000000 : ℝ)|=(3728792993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2341639257/5000000000 : ℝ)|^4847 ≤ (3822134673103/10000000000000 : ℝ)^3823
        have hw : |(2341639257/5000000000 : ℝ)|=(2341639257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s1_4 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-819237061/5000000000 : ℝ)*x 0 + (5136960149/10000000000 : ℝ)*x 1 + (275323689/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (819237061/5000000000 : ℝ)^4847 ≤ (2523279135749/25000000000000 : ℝ)^3823 := by
    have hnat : (819237061 : ℕ)^4847*25000000000000^3823 ≤ 2523279135749^3823*5000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      819237061 5000000000 2523279135749 25000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5136960149/10000000000 : ℝ)^4847 ≤ (8595044547323/20000000000000 : ℝ)^3823 := by
    have hnat : (5136960149 : ℕ)^4847*20000000000000^3823 ≤ 8595044547323^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5136960149 10000000000 8595044547323 20000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275323689/500000000 : ℝ)^4847 ≤ (11732915177261/25000000000000 : ℝ)^3823 := by
    have hnat : (275323689 : ℕ)^4847*25000000000000^3823 ≤ 11732915177261^3823*500000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275323689 500000000 11732915177261 25000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-819237061/5000000000 : ℝ), (5136960149/10000000000 : ℝ), (275323689/500000000 : ℝ)] ![(2523279135749/25000000000000 : ℝ), (8595044547323/20000000000000 : ℝ), (11732915177261/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-819237061/5000000000 : ℝ)|^4847 ≤ (2523279135749/25000000000000 : ℝ)^3823
        have hw : |(-819237061/5000000000 : ℝ)|=(819237061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5136960149/10000000000 : ℝ)|^4847 ≤ (8595044547323/20000000000000 : ℝ)^3823
        have hw : |(5136960149/10000000000 : ℝ)|=(5136960149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(275323689/500000000 : ℝ)|^4847 ≤ (11732915177261/25000000000000 : ℝ)^3823
        have hw : |(275323689/500000000 : ℝ)|=(275323689/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s1_5 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1052973969/2000000000 : ℝ)*x 0 + (-1461556693/10000000000 : ℝ)*x 1 + (5506474147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052973969/2000000000 : ℝ)^4847 ≤ (4433642073791/10000000000000 : ℝ)^3823 := by
    have hnat : (1052973969 : ℕ)^4847*10000000000000^3823 ≤ 4433642073791^3823*2000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052973969 2000000000 4433642073791 10000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1461556693/10000000000 : ℝ)^4847 ≤ (545744660221/6250000000000 : ℝ)^3823 := by
    have hnat : (1461556693 : ℕ)^4847*6250000000000^3823 ≤ 545744660221^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1461556693 10000000000 545744660221 6250000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5506474147/10000000000 : ℝ)^4847 ≤ (46931664674811/100000000000000 : ℝ)^3823 := by
    have hnat : (5506474147 : ℕ)^4847*100000000000000^3823 ≤ 46931664674811^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5506474147 10000000000 46931664674811 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1052973969/2000000000 : ℝ), (-1461556693/10000000000 : ℝ), (5506474147/10000000000 : ℝ)] ![(4433642073791/10000000000000 : ℝ), (545744660221/6250000000000 : ℝ), (46931664674811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1052973969/2000000000 : ℝ)|^4847 ≤ (4433642073791/10000000000000 : ℝ)^3823
        have hw : |(1052973969/2000000000 : ℝ)|=(1052973969/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1461556693/10000000000 : ℝ)|^4847 ≤ (545744660221/6250000000000 : ℝ)^3823
        have hw : |(-1461556693/10000000000 : ℝ)|=(1461556693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5506474147/10000000000 : ℝ)|^4847 ≤ (46931664674811/100000000000000 : ℝ)^3823
        have hw : |(5506474147/10000000000 : ℝ)|=(5506474147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s1_6 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (329054323/625000000 : ℝ)*x 0 + (1101294879/2000000000 : ℝ)*x 1 + (-91347331/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329054323/625000000 : ℝ)^4847 ≤ (44336413509707/100000000000000 : ℝ)^3823 := by
    have hnat : (329054323 : ℕ)^4847*100000000000000^3823 ≤ 44336413509707^3823*625000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329054323 625000000 44336413509707 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1101294879/2000000000 : ℝ)^4847 ≤ (1877266694187/4000000000000 : ℝ)^3823 := by
    have hnat : (1101294879 : ℕ)^4847*4000000000000^3823 ≤ 1877266694187^3823*2000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101294879 2000000000 1877266694187 4000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (91347331/625000000 : ℝ)^4847 ≤ (174638382621/2000000000000 : ℝ)^3823 := by
    have hnat : (91347331 : ℕ)^4847*2000000000000^3823 ≤ 174638382621^3823*625000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91347331 625000000 174638382621 2000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(329054323/625000000 : ℝ), (1101294879/2000000000 : ℝ), (-91347331/625000000 : ℝ)] ![(44336413509707/100000000000000 : ℝ), (1877266694187/4000000000000 : ℝ), (174638382621/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(329054323/625000000 : ℝ)|^4847 ≤ (44336413509707/100000000000000 : ℝ)^3823
        have hw : |(329054323/625000000 : ℝ)|=(329054323/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1101294879/2000000000 : ℝ)|^4847 ≤ (1877266694187/4000000000000 : ℝ)^3823
        have hw : |(1101294879/2000000000 : ℝ)|=(1101294879/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-91347331/625000000 : ℝ)|^4847 ≤ (174638382621/2000000000000 : ℝ)^3823
        have hw : |(-91347331/625000000 : ℝ)|=(91347331/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s1_7 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4186283799/10000000000 : ℝ)*x 0 + (1168325337/2500000000 : ℝ)*x 1 + (116841187/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4186283799/10000000000 : ℝ)^4847 ≤ (8288473423383/25000000000000 : ℝ)^3823 := by
    have hnat : (4186283799 : ℕ)^4847*25000000000000^3823 ≤ 8288473423383^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4186283799 10000000000 8288473423383 25000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1168325337/2500000000 : ℝ)^4847 ≤ (38118140022739/100000000000000 : ℝ)^3823 := by
    have hnat : (1168325337 : ℕ)^4847*100000000000000^3823 ≤ 38118140022739^3823*2500000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1168325337 2500000000 38118140022739 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (116841187/312500000 : ℝ)^4847 ≤ (14363983135951/50000000000000 : ℝ)^3823 := by
    have hnat : (116841187 : ℕ)^4847*50000000000000^3823 ≤ 14363983135951^3823*312500000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116841187 312500000 14363983135951 50000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4186283799/10000000000 : ℝ), (1168325337/2500000000 : ℝ), (116841187/312500000 : ℝ)] ![(8288473423383/25000000000000 : ℝ), (38118140022739/100000000000000 : ℝ), (14363983135951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4186283799/10000000000 : ℝ)|^4847 ≤ (8288473423383/25000000000000 : ℝ)^3823
        have hw : |(4186283799/10000000000 : ℝ)|=(4186283799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1168325337/2500000000 : ℝ)|^4847 ≤ (38118140022739/100000000000000 : ℝ)^3823
        have hw : |(1168325337/2500000000 : ℝ)|=(1168325337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(116841187/312500000 : ℝ)|^4847 ≤ (14363983135951/50000000000000 : ℝ)^3823
        have hw : |(116841187/312500000 : ℝ)|=(116841187/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1632_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (176433729/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11873/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2243/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (9497/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17507/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (11873/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2243/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (11873/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2243/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (11873/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2243/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (11873/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2243/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (11873/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2243/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (11873/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2243/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2243/50000 : ℝ) ^ (4843/1024 : ℝ) ≤ (42070623287473/100000000000000000000 : ℝ) := by
    have hpowers : (2243/50000 : ℝ)^4843 ≤ (42070623287473/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2243 : ℕ)^4843*100000000000000000000^1024 ≤ 42070623287473^1024*50000^4843 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2243 50000 42070623287473 100000000000000000000 4843 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2243/50000 : ℝ)) (X := (42070623287473/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4843 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (11873/50000 : ℝ) ^ (4843/1024 : ℝ) ≤ (111393532166793353/100000000000000000000 : ℝ) := by
    have hpowers : (11873/50000 : ℝ)^4843 ≤ (111393532166793353/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11873 : ℕ)^4843*100000000000000000000^1024 ≤ 111393532166793353^1024*50000^4843 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11873 50000 111393532166793353 100000000000000000000 4843 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11873/50000 : ℝ)) (X := (111393532166793353/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4843 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000042070623287473/50000000000000000000 : ℝ) ≤ (10000001779075117/10000000000000000 : ℝ) ^ (4843/1024 : ℝ) := by
    have hpowers : (50000042070623287473/50000000000000000000 : ℝ)^1024 ≤ (10000001779075117/10000000000000000 : ℝ)^4843 := by
      have hnat : (50000042070623287473 : ℕ)^1024*10000000000000000^4843 ≤ 10000001779075117^4843*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000042070623287473 50000000000000000000 10000001779075117 10000000000000000 1024 4843 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001779075117/10000000000000000 : ℝ)) (X := (50000042070623287473/50000000000000000000 : ℝ)) (by norm_num) 4843 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50055717801395040413/50000000000000000000 : ℝ) ≤ (2500588787704663/2500000000000000 : ℝ) ^ (4843/1024 : ℝ) := by
    have hpowers : (50055717801395040413/50000000000000000000 : ℝ)^1024 ≤ (2500588787704663/2500000000000000 : ℝ)^4843 := by
      have hnat : (50055717801395040413 : ℕ)^1024*2500000000000000^4843 ≤ 2500588787704663^4843*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50055717801395040413 50000000000000000000 2500588787704663 2500000000000000 1024 4843 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500588787704663/2500000000000000 : ℝ)) (X := (50055717801395040413/50000000000000000000 : ℝ)) (by norm_num) 4843 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50111393532166793353/50000000000000000000 : ℝ) ≤ (10004708522562187/10000000000000000 : ℝ) ^ (4843/1024 : ℝ) := by
    have hpowers : (50111393532166793353/50000000000000000000 : ℝ)^1024 ≤ (10004708522562187/10000000000000000 : ℝ)^4843 := by
      have hnat : (50111393532166793353 : ℕ)^1024*10000000000000000^4843 ≤ 10004708522562187^4843*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50111393532166793353 50000000000000000000 10004708522562187 10000000000000000 1024 4843 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004708522562187/10000000000000000 : ℝ)) (X := (50111393532166793353/50000000000000000000 : ℝ)) (by norm_num) 4843 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(42070623287473/100000000000000000000 : ℝ) ≤ ((320964866356172929/321000000000000000 : ℝ)+2*(156891449569/128400000000000 : ℝ)*(2243/50000 : ℝ))^(4843/1024 : ℝ) := by
    rw [show (320964866356172929/321000000000000000 : ℝ)+2*(156891449569/128400000000000 : ℝ)*(2243/50000 : ℝ)=(10000001779075117/10000000000000000 : ℝ) by norm_num, show 1+2*(42070623287473/100000000000000000000 : ℝ)=(50000042070623287473/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(111393532166793353/100000000000000000000 : ℝ)+(42070623287473/100000000000000000000 : ℝ) ≤ ((320964866356172929/321000000000000000 : ℝ)+(156891449569/128400000000000 : ℝ)*((11873/50000 : ℝ)+(2243/50000 : ℝ)))^(4843/1024 : ℝ) := by
    rw [show (320964866356172929/321000000000000000 : ℝ)+(156891449569/128400000000000 : ℝ)*((11873/50000 : ℝ)+(2243/50000 : ℝ))=(2500588787704663/2500000000000000 : ℝ) by norm_num, show 1+(111393532166793353/100000000000000000000 : ℝ)+(42070623287473/100000000000000000000 : ℝ)=(50055717801395040413/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(111393532166793353/100000000000000000000 : ℝ) ≤ ((320964866356172929/321000000000000000 : ℝ)+2*(156891449569/128400000000000 : ℝ)*(11873/50000 : ℝ))^(4843/1024 : ℝ) := by
    rw [show (320964866356172929/321000000000000000 : ℝ)+2*(156891449569/128400000000000 : ℝ)*(11873/50000 : ℝ)=(10004708522562187/10000000000000000 : ℝ) by norm_num, show 1+2*(111393532166793353/100000000000000000000 : ℝ)=(50111393532166793353/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (320964866356172929/321000000000000000 : ℝ)*(X 1 0+X 2 0)+(156891449569/128400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4843/1024 : ℝ)) (lo := (2243/50000 : ℝ)) (hi := (11873/50000 : ℝ)) (c := (320964866356172929/321000000000000000 : ℝ)) (alpha := (156891449569/128400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (320964866356172929/321000000000000000 : ℝ)*(X 0 1+X 2 1)+(156891449569/128400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4843/1024 : ℝ)) (lo := (2243/50000 : ℝ)) (hi := (11873/50000 : ℝ)) (c := (320964866356172929/321000000000000000 : ℝ)) (alpha := (156891449569/128400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (320964866356172929/321000000000000000 : ℝ)*(X 0 2+X 1 2)+(156891449569/128400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4843/1024 : ℝ)) (lo := (2243/50000 : ℝ)) (hi := (11873/50000 : ℝ)) (c := (320964866356172929/321000000000000000 : ℝ)) (alpha := (156891449569/128400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-819145683/5000000000 : ℝ)*X 0 0+(5510478247/10000000000 : ℝ)*X 0 1+(2566507121/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1073117819/2000000000 : ℝ)*X 1 0+(-91750867/500000000 : ℝ)*X 1 1+(2566507007/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1073117983/2000000000 : ℝ)*X 2 0+(1026602603/2000000000 : ℝ)*X 2 1+(-1835017561/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4185824723/10000000000 : ℝ)*X 0 0+(3728792993/10000000000 : ℝ)*X 0 1+(2341639257/5000000000 : ℝ)*X 0 2+(4185824723/10000000000 : ℝ)*X 1 0+(3728792993/10000000000 : ℝ)*X 1 1+(2341639257/5000000000 : ℝ)*X 1 2+(4185824723/10000000000 : ℝ)*X 2 0+(3728792993/10000000000 : ℝ)*X 2 1+(2341639257/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-819237061/5000000000 : ℝ)*X 0 0+(5136960149/10000000000 : ℝ)*X 0 1+(275323689/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1052973969/2000000000 : ℝ)*X 1 0+(-1461556693/10000000000 : ℝ)*X 1 1+(5506474147/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((329054323/625000000 : ℝ)*X 2 0+(1101294879/2000000000 : ℝ)*X 2 1+(-91347331/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4186283799/10000000000 : ℝ)*X 0 0+(1168325337/2500000000 : ℝ)*X 0 1+(116841187/312500000 : ℝ)*X 0 2+(4186283799/10000000000 : ℝ)*X 1 0+(1168325337/2500000000 : ℝ)*X 1 1+(116841187/312500000 : ℝ)*X 1 2+(4186283799/10000000000 : ℝ)*X 2 0+(1168325337/2500000000 : ℝ)*X 2 1+(116841187/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (250829237721574341319987/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (44975063/12500000000000 : ℝ)*(base1) + (30487947/5000000000000 : ℝ)*(base19) + (557928877/50000000000000 : ℝ)*(base23) + (5167963/10000000000000 : ℝ)*(upper3) + (5431277/10000000000000 : ℝ)*(lower4) + (34719213/50000000000000 : ℝ)*(upper5) + (1848472264339921/100000000000000 : ℝ)*(major0) + (1848472264339921/100000000000000 : ℝ)*(major1) + (1848472264339921/100000000000000 : ℝ)*(major2) + (2649258275581337/100000000000000 : ℝ)*(sp0) + (2649257306021893/100000000000000 : ℝ)*(sp1) + (66231419998077/2500000000000 : ℝ)*(sp2) + (1047685363144323/100000000000000 : ℝ)*(sp3) + (144546937/20000000000000 : ℝ)*(sp7) + (1047686445679511/100000000000000 : ℝ)*(f.failure) + (2649257915780833/100000000000000 : ℝ)*(f.sum) + (53659948213/60000000000000000000000000 : ℝ)*base66 + (342958997967487/300000000000000000000000000000 : ℝ)*base67 + (725098679432513/300000000000000000000000000000 : ℝ)*base70 + (100930301667487/300000000000000000000000000000 : ℝ)*base71 + (32589748033/60000000000000000000000000 : ℝ)*base74 + (637920763832513/300000000000000000000000000000 : ℝ)*base76 + (1072574107832513/300000000000000000000000000000 : ℝ)*base78 + (3203403990332513/300000000000000000000000000000 : ℝ)*base80 + (147338769013/60000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (35373481/10000000000000000000000 : ℝ)*base90 + (35373481/10000000000000000000000 : ℝ)*base92 + (35373481/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18181596068055088002419/2140000000000000000000000000 : ℝ) := by norm_num
    linear_combination (418958957/25000000000000 : ℝ)*(base19) + (174183671/12500000000000 : ℝ)*(base23) + (1217831/3125000000000 : ℝ)*(upper2) + (23589763/6250000000000 : ℝ)*(upper3) + (61794559/100000000000000 : ℝ)*(upper5) + (1888239462433669/100000000000000 : ℝ)*(major0) + (1888239462433669/100000000000000 : ℝ)*(major1) + (1888239462433669/100000000000000 : ℝ)*(major2) + (794804429/6250000000000 : ℝ)*(sp1) + (12277880333/100000000000000 : ℝ)*(sp2) + (2706252742605843/100000000000000 : ℝ)*(sp4) + (169139896868697/6250000000000 : ℝ)*(sp5) + (1353119535628071/50000000000000 : ℝ)*(sp6) + (66889118691191/6250000000000 : ℝ)*(sp7) + (66889118691191/6250000000000 : ℝ)*(f.failure) + (2706252742605843/100000000000000 : ℝ)*(f.sum) + (19348961413501/6420000000000000000000000000 : ℝ)*base65 + (104292312646900999/32100000000000000000000000000000 : ℝ)*base68 + (353216097630199001/32100000000000000000000000000000 : ℝ)*base69 + (74521975571800999/32100000000000000000000000000000 : ℝ)*base72 + (19167587797979/6420000000000000000000000000 : ℝ)*base74 + (171015900659800999/32100000000000000000000000000000 : ℝ)*base76 + (92058662233099001/32100000000000000000000000000000 : ℝ)*base77 + (139492181309299001/32100000000000000000000000000000 : ℝ)*base79 + (37681371815881/6420000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (3668761/625000000000000000000 : ℝ)*base90 + (3668761/625000000000000000000 : ℝ)*base92 + (3668761/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1632_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (176433729/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11873/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2243/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9497/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17507/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1632_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1632_s2_0 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1649452217/10000000000 : ℝ)*x 0 + (682220187/1250000000 : ℝ)*x 1 + (1294598223/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1649452217/10000000000 : ℝ)^4847 ≤ (5089466472741/50000000000000 : ℝ)^3823 := by
    have hnat : (1649452217 : ℕ)^4847*50000000000000^3823 ≤ 5089466472741^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1649452217 10000000000 5089466472741 50000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (682220187/1250000000 : ℝ)^4847 ≤ (46405905474893/100000000000000 : ℝ)^3823 := by
    have hnat : (682220187 : ℕ)^4847*100000000000000^3823 ≤ 46405905474893^3823*1250000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682220187 1250000000 46405905474893 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294598223/2500000000 : ℝ)^4847 ≤ (8683032314013/20000000000000 : ℝ)^3823 := by
    have hnat : (1294598223 : ℕ)^4847*20000000000000^3823 ≤ 8683032314013^3823*2500000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294598223 2500000000 8683032314013 20000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1649452217/10000000000 : ℝ), (682220187/1250000000 : ℝ), (1294598223/2500000000 : ℝ)] ![(5089466472741/50000000000000 : ℝ), (46405905474893/100000000000000 : ℝ), (8683032314013/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1649452217/10000000000 : ℝ)|^4847 ≤ (5089466472741/50000000000000 : ℝ)^3823
        have hw : |(-1649452217/10000000000 : ℝ)|=(1649452217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(682220187/1250000000 : ℝ)|^4847 ≤ (46405905474893/100000000000000 : ℝ)^3823
        have hw : |(682220187/1250000000 : ℝ)|=(682220187/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1294598223/2500000000 : ℝ)|^4847 ≤ (8683032314013/20000000000000 : ℝ)^3823
        have hw : |(1294598223/2500000000 : ℝ)|=(1294598223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s2_1 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351727607/10000000000 : ℝ)*x 0 + (-1793516559/10000000000 : ℝ)*x 1 + (2589196459/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351727607/10000000000 : ℝ)^4847 ≤ (11316456441957/25000000000000 : ℝ)^3823 := by
    have hnat : (5351727607 : ℕ)^4847*25000000000000^3823 ≤ 11316456441957^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351727607 10000000000 11316456441957 25000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1793516559/10000000000 : ℝ)^4847 ≤ (1131901237937/10000000000000 : ℝ)^3823 := by
    have hnat : (1793516559 : ℕ)^4847*10000000000000^3823 ≤ 1131901237937^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1793516559 10000000000 1131901237937 10000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2589196459/5000000000 : ℝ)^4847 ≤ (21707580923217/50000000000000 : ℝ)^3823 := by
    have hnat : (2589196459 : ℕ)^4847*50000000000000^3823 ≤ 21707580923217^3823*5000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589196459 5000000000 21707580923217 50000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351727607/10000000000 : ℝ), (-1793516559/10000000000 : ℝ), (2589196459/5000000000 : ℝ)] ![(11316456441957/25000000000000 : ℝ), (1131901237937/10000000000000 : ℝ), (21707580923217/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351727607/10000000000 : ℝ)|^4847 ≤ (11316456441957/25000000000000 : ℝ)^3823
        have hw : |(5351727607/10000000000 : ℝ)|=(5351727607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1793516559/10000000000 : ℝ)|^4847 ≤ (1131901237937/10000000000000 : ℝ)^3823
        have hw : |(-1793516559/10000000000 : ℝ)|=(1793516559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2589196459/5000000000 : ℝ)|^4847 ≤ (21707580923217/50000000000000 : ℝ)^3823
        have hw : |(2589196459/5000000000 : ℝ)|=(2589196459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s2_2 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351727613/10000000000 : ℝ)*x 0 + (5178392881/10000000000 : ℝ)*x 1 + (-1793516599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351727613/10000000000 : ℝ)^4847 ≤ (45265825832171/100000000000000 : ℝ)^3823 := by
    have hnat : (5351727613 : ℕ)^4847*100000000000000^3823 ≤ 45265825832171^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351727613 10000000000 45265825832171 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5178392881/10000000000 : ℝ)^4847 ≤ (2170758072657/5000000000000 : ℝ)^3823 := by
    have hnat : (5178392881 : ℕ)^4847*5000000000000^3823 ≤ 2170758072657^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178392881 10000000000 2170758072657 5000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1793516599/10000000000 : ℝ)^4847 ≤ (11319012699431/100000000000000 : ℝ)^3823 := by
    have hnat : (1793516599 : ℕ)^4847*100000000000000^3823 ≤ 11319012699431^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1793516599 10000000000 11319012699431 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351727613/10000000000 : ℝ), (5178392881/10000000000 : ℝ), (-1793516599/10000000000 : ℝ)] ![(45265825832171/100000000000000 : ℝ), (2170758072657/5000000000000 : ℝ), (11319012699431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351727613/10000000000 : ℝ)|^4847 ≤ (45265825832171/100000000000000 : ℝ)^3823
        have hw : |(5351727613/10000000000 : ℝ)|=(5351727613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5178392881/10000000000 : ℝ)|^4847 ≤ (2170758072657/5000000000000 : ℝ)^3823
        have hw : |(5178392881/10000000000 : ℝ)|=(5178392881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1793516599/10000000000 : ℝ)|^4847 ≤ (11319012699431/100000000000000 : ℝ)^3823
        have hw : |(-1793516599/10000000000 : ℝ)|=(1793516599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s2_3 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1048527111/2500000000 : ℝ)*x 0 + (770393599/2000000000 : ℝ)*x 1 + (4558400213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1048527111/2500000000 : ℝ)^4847 ≤ (8308120045769/25000000000000 : ℝ)^3823 := by
    have hnat : (1048527111 : ℕ)^4847*25000000000000^3823 ≤ 8308120045769^3823*2500000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048527111 2500000000 8308120045769 25000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (770393599/2000000000 : ℝ)^4847 ≤ (298336746373/1000000000000 : ℝ)^3823 := by
    have hnat : (770393599 : ℕ)^4847*1000000000000^3823 ≤ 298336746373^3823*2000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      770393599 2000000000 298336746373 1000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4558400213/10000000000 : ℝ)^4847 ≤ (3693384515959/10000000000000 : ℝ)^3823 := by
    have hnat : (4558400213 : ℕ)^4847*10000000000000^3823 ≤ 3693384515959^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4558400213 10000000000 3693384515959 10000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1048527111/2500000000 : ℝ), (770393599/2000000000 : ℝ), (4558400213/10000000000 : ℝ)] ![(8308120045769/25000000000000 : ℝ), (298336746373/1000000000000 : ℝ), (3693384515959/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1048527111/2500000000 : ℝ)|^4847 ≤ (8308120045769/25000000000000 : ℝ)^3823
        have hw : |(1048527111/2500000000 : ℝ)|=(1048527111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(770393599/2000000000 : ℝ)|^4847 ≤ (298336746373/1000000000000 : ℝ)^3823
        have hw : |(770393599/2000000000 : ℝ)|=(770393599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4558400213/10000000000 : ℝ)|^4847 ≤ (3693384515959/10000000000000 : ℝ)^3823
        have hw : |(4558400213/10000000000 : ℝ)|=(4558400213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s2_4 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1649525781/10000000000 : ℝ)*x 0 + (161892539/312500000 : ℝ)*x 1 + (2727784907/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1649525781/10000000000 : ℝ)^4847 ≤ (10179508516829/100000000000000 : ℝ)^3823 := by
    have hnat : (1649525781 : ℕ)^4847*100000000000000^3823 ≤ 10179508516829^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1649525781 10000000000 10179508516829 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (161892539/312500000 : ℝ)^4847 ≤ (43438211525133/100000000000000 : ℝ)^3823 := by
    have hnat : (161892539 : ℕ)^4847*100000000000000^3823 ≤ 43438211525133^3823*312500000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161892539 312500000 43438211525133 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2727784907/5000000000 : ℝ)^4847 ≤ (46382279942671/100000000000000 : ℝ)^3823 := by
    have hnat : (2727784907 : ℕ)^4847*100000000000000^3823 ≤ 46382279942671^3823*5000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2727784907 5000000000 46382279942671 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1649525781/10000000000 : ℝ), (161892539/312500000 : ℝ), (2727784907/5000000000 : ℝ)] ![(10179508516829/100000000000000 : ℝ), (43438211525133/100000000000000 : ℝ), (46382279942671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1649525781/10000000000 : ℝ)|^4847 ≤ (10179508516829/100000000000000 : ℝ)^3823
        have hw : |(-1649525781/10000000000 : ℝ)|=(1649525781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(161892539/312500000 : ℝ)|^4847 ≤ (43438211525133/100000000000000 : ℝ)^3823
        have hw : |(161892539/312500000 : ℝ)|=(161892539/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2727784907/5000000000 : ℝ)|^4847 ≤ (46382279942671/100000000000000 : ℝ)^3823
        have hw : |(2727784907/5000000000 : ℝ)|=(2727784907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s2_5 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055452553/2000000000 : ℝ)*x 0 + (-758169759/5000000000 : ℝ)*x 1 + (1065541/1953125 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055452553/2000000000 : ℝ)^4847 ≤ (8893755867807/20000000000000 : ℝ)^3823 := by
    have hnat : (1055452553 : ℕ)^4847*20000000000000^3823 ≤ 8893755867807^3823*2000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055452553 2000000000 8893755867807 20000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (758169759/5000000000 : ℝ)^4847 ≤ (9148939559887/100000000000000 : ℝ)^3823 := by
    have hnat : (758169759 : ℕ)^4847*100000000000000^3823 ≤ 9148939559887^3823*5000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      758169759 5000000000 9148939559887 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1065541/1953125 : ℝ)^4847 ≤ (185529124341/400000000000 : ℝ)^3823 := by
    have hnat : (1065541 : ℕ)^4847*400000000000^3823 ≤ 185529124341^3823*1953125^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065541 1953125 185529124341 400000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055452553/2000000000 : ℝ), (-758169759/5000000000 : ℝ), (1065541/1953125 : ℝ)] ![(8893755867807/20000000000000 : ℝ), (9148939559887/100000000000000 : ℝ), (185529124341/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055452553/2000000000 : ℝ)|^4847 ≤ (8893755867807/20000000000000 : ℝ)^3823
        have hw : |(1055452553/2000000000 : ℝ)|=(1055452553/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-758169759/5000000000 : ℝ)|^4847 ≤ (9148939559887/100000000000000 : ℝ)^3823
        have hw : |(-758169759/5000000000 : ℝ)|=(758169759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1065541/1953125 : ℝ)|^4847 ≤ (185529124341/400000000000 : ℝ)^3823
        have hw : |(1065541/1953125 : ℝ)|=(1065541/1953125 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s2_6 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277263673/10000000000 : ℝ)*x 0 + (2727784437/5000000000 : ℝ)*x 1 + (-379084931/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277263673/10000000000 : ℝ)^4847 ≤ (4446878903969/10000000000000 : ℝ)^3823 := by
    have hnat : (5277263673 : ℕ)^4847*10000000000000^3823 ≤ 4446878903969^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277263673 10000000000 4446878903969 10000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2727784437/5000000000 : ℝ)^4847 ≤ (46382269810359/100000000000000 : ℝ)^3823 := by
    have hnat : (2727784437 : ℕ)^4847*100000000000000^3823 ≤ 46382269810359^3823*5000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2727784437 5000000000 46382269810359 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (379084931/2500000000 : ℝ)^4847 ≤ (228723528393/2500000000000 : ℝ)^3823 := by
    have hnat : (379084931 : ℕ)^4847*2500000000000^3823 ≤ 228723528393^3823*2500000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379084931 2500000000 228723528393 2500000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277263673/10000000000 : ℝ), (2727784437/5000000000 : ℝ), (-379084931/2500000000 : ℝ)] ![(4446878903969/10000000000000 : ℝ), (46382269810359/100000000000000 : ℝ), (228723528393/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277263673/10000000000 : ℝ)|^4847 ≤ (4446878903969/10000000000000 : ℝ)^3823
        have hw : |(5277263673/10000000000 : ℝ)|=(5277263673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2727784437/5000000000 : ℝ)|^4847 ≤ (46382269810359/100000000000000 : ℝ)^3823
        have hw : |(2727784437/5000000000 : ℝ)|=(2727784437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-379084931/2500000000 : ℝ)|^4847 ≤ (228723528393/2500000000000 : ℝ)^3823
        have hw : |(-379084931/2500000000 : ℝ)|=(379084931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s2_7 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2097147563/5000000000 : ℝ)*x 0 + (4552918929/10000000000 : ℝ)*x 1 + (60273581/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2097147563/5000000000 : ℝ)^4847 ≤ (4154294449473/12500000000000 : ℝ)^3823 := by
    have hnat : (2097147563 : ℕ)^4847*12500000000000^3823 ≤ 4154294449473^3823*5000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097147563 5000000000 4154294449473 12500000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4552918929/10000000000 : ℝ)^4847 ≤ (3687754713803/10000000000000 : ℝ)^3823 := by
    have hnat : (4552918929 : ℕ)^4847*10000000000000^3823 ≤ 3687754713803^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4552918929 10000000000 3687754713803 10000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (60273581/156250000 : ℝ)^4847 ≤ (1868006078199/6250000000000 : ℝ)^3823 := by
    have hnat : (60273581 : ℕ)^4847*6250000000000^3823 ≤ 1868006078199^3823*156250000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60273581 156250000 1868006078199 6250000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2097147563/5000000000 : ℝ), (4552918929/10000000000 : ℝ), (60273581/156250000 : ℝ)] ![(4154294449473/12500000000000 : ℝ), (3687754713803/10000000000000 : ℝ), (1868006078199/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2097147563/5000000000 : ℝ)|^4847 ≤ (4154294449473/12500000000000 : ℝ)^3823
        have hw : |(2097147563/5000000000 : ℝ)|=(2097147563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4552918929/10000000000 : ℝ)|^4847 ≤ (3687754713803/10000000000000 : ℝ)^3823
        have hw : |(4552918929/10000000000 : ℝ)|=(4552918929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(60273581/156250000 : ℝ)|^4847 ≤ (1868006078199/6250000000000 : ℝ)^3823
        have hw : |(60273581/156250000 : ℝ)|=(60273581/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1632_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (176433729/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17507/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9497/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10477/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2051/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17507/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9497/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17507/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9497/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17507/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9497/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17507/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9497/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17507/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9497/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17507/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9497/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9497/100000 : ℝ) ^ (4843/1024 : ℝ) ≤ (365126248350019/25000000000000000000 : ℝ) := by
    have hpowers : (9497/100000 : ℝ)^4843 ≤ (365126248350019/25000000000000000000 : ℝ)^1024 := by
      have hnat : (9497 : ℕ)^4843*25000000000000000000^1024 ≤ 365126248350019^1024*100000^4843 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9497 100000 365126248350019 25000000000000000000 4843 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9497/100000 : ℝ)) (X := (365126248350019/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4843 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17507/100000 : ℝ) ^ (4843/1024 : ℝ) ≤ (26349707444748819/100000000000000000000 : ℝ) := by
    have hpowers : (17507/100000 : ℝ)^4843 ≤ (26349707444748819/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17507 : ℕ)^4843*100000000000000000000^1024 ≤ 26349707444748819^1024*100000^4843 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17507 100000 26349707444748819 100000000000000000000 4843 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17507/100000 : ℝ)) (X := (26349707444748819/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4843 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500365126248350019/12500000000000000000 : ℝ) ≤ (2500015440221859/2500000000000000 : ℝ) ^ (4843/1024 : ℝ) := by
    have hpowers : (12500365126248350019/12500000000000000000 : ℝ)^1024 ≤ (2500015440221859/2500000000000000 : ℝ)^4843 := by
      have hnat : (12500365126248350019 : ℕ)^1024*2500000000000000^4843 ≤ 2500015440221859^4843*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500365126248350019 12500000000000000000 2500015440221859 2500000000000000 1024 4843 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500015440221859/2500000000000000 : ℝ)) (X := (12500365126248350019/12500000000000000000 : ℝ)) (by norm_num) 4843 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20005562042487629779/20000000000000000000 : ℝ) ≤ (10000587952415299/10000000000000000 : ℝ) ^ (4843/1024 : ℝ) := by
    have hpowers : (20005562042487629779/20000000000000000000 : ℝ)^1024 ≤ (10000587952415299/10000000000000000 : ℝ)^4843 := by
      have hnat : (20005562042487629779 : ℕ)^1024*10000000000000000^4843 ≤ 10000587952415299^4843*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20005562042487629779 20000000000000000000 10000587952415299 10000000000000000 1024 4843 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000587952415299/10000000000000000 : ℝ)) (X := (20005562042487629779/20000000000000000000 : ℝ)) (by norm_num) 4843 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026349707444748819/50000000000000000000 : ℝ) ≤ (5000557071971581/5000000000000000 : ℝ) ^ (4843/1024 : ℝ) := by
    have hpowers : (50026349707444748819/50000000000000000000 : ℝ)^1024 ≤ (5000557071971581/5000000000000000 : ℝ)^4843 := by
      have hnat : (50026349707444748819 : ℕ)^1024*5000000000000000^4843 ≤ 5000557071971581^4843*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026349707444748819 50000000000000000000 5000557071971581 5000000000000000 1024 4843 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000557071971581/5000000000000000 : ℝ)) (X := (50026349707444748819/50000000000000000000 : ℝ)) (by norm_num) 4843 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(365126248350019/25000000000000000000 : ℝ) ≤ ((40045250111414066269/40050000000000000000 : ℝ)+2*(526191527863/801000000000000 : ℝ)*(9497/100000 : ℝ))^(4843/1024 : ℝ) := by
    rw [show (40045250111414066269/40050000000000000000 : ℝ)+2*(526191527863/801000000000000 : ℝ)*(9497/100000 : ℝ)=(2500015440221859/2500000000000000 : ℝ) by norm_num, show 1+2*(365126248350019/25000000000000000000 : ℝ)=(12500365126248350019/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26349707444748819/100000000000000000000 : ℝ)+(365126248350019/25000000000000000000 : ℝ) ≤ ((40045250111414066269/40050000000000000000 : ℝ)+(526191527863/801000000000000 : ℝ)*((17507/100000 : ℝ)+(9497/100000 : ℝ)))^(4843/1024 : ℝ) := by
    rw [show (40045250111414066269/40050000000000000000 : ℝ)+(526191527863/801000000000000 : ℝ)*((17507/100000 : ℝ)+(9497/100000 : ℝ))=(10000587952415299/10000000000000000 : ℝ) by norm_num, show 1+(26349707444748819/100000000000000000000 : ℝ)+(365126248350019/25000000000000000000 : ℝ)=(20005562042487629779/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26349707444748819/100000000000000000000 : ℝ) ≤ ((40045250111414066269/40050000000000000000 : ℝ)+2*(526191527863/801000000000000 : ℝ)*(17507/100000 : ℝ))^(4843/1024 : ℝ) := by
    rw [show (40045250111414066269/40050000000000000000 : ℝ)+2*(526191527863/801000000000000 : ℝ)*(17507/100000 : ℝ)=(5000557071971581/5000000000000000 : ℝ) by norm_num, show 1+2*(26349707444748819/100000000000000000000 : ℝ)=(50026349707444748819/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (40045250111414066269/40050000000000000000 : ℝ)*(X 1 0+X 2 0)+(526191527863/801000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4843/1024 : ℝ)) (lo := (9497/100000 : ℝ)) (hi := (17507/100000 : ℝ)) (c := (40045250111414066269/40050000000000000000 : ℝ)) (alpha := (526191527863/801000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (40045250111414066269/40050000000000000000 : ℝ)*(X 0 1+X 2 1)+(526191527863/801000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4843/1024 : ℝ)) (lo := (9497/100000 : ℝ)) (hi := (17507/100000 : ℝ)) (c := (40045250111414066269/40050000000000000000 : ℝ)) (alpha := (526191527863/801000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (40045250111414066269/40050000000000000000 : ℝ)*(X 0 2+X 1 2)+(526191527863/801000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4843/1024 : ℝ)) (lo := (9497/100000 : ℝ)) (hi := (17507/100000 : ℝ)) (c := (40045250111414066269/40050000000000000000 : ℝ)) (alpha := (526191527863/801000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1649452217/10000000000 : ℝ)*X 0 0+(682220187/1250000000 : ℝ)*X 0 1+(1294598223/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351727607/10000000000 : ℝ)*X 1 0+(-1793516559/10000000000 : ℝ)*X 1 1+(2589196459/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351727613/10000000000 : ℝ)*X 2 0+(5178392881/10000000000 : ℝ)*X 2 1+(-1793516599/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1048527111/2500000000 : ℝ)*X 0 0+(770393599/2000000000 : ℝ)*X 0 1+(4558400213/10000000000 : ℝ)*X 0 2+(1048527111/2500000000 : ℝ)*X 1 0+(770393599/2000000000 : ℝ)*X 1 1+(4558400213/10000000000 : ℝ)*X 1 2+(1048527111/2500000000 : ℝ)*X 2 0+(770393599/2000000000 : ℝ)*X 2 1+(4558400213/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1649525781/10000000000 : ℝ)*X 0 0+(161892539/312500000 : ℝ)*X 0 1+(2727784907/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1055452553/2000000000 : ℝ)*X 1 0+(-758169759/5000000000 : ℝ)*X 1 1+(1065541/1953125 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5277263673/10000000000 : ℝ)*X 2 0+(2727784437/5000000000 : ℝ)*X 2 1+(-379084931/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2097147563/5000000000 : ℝ)*X 0 0+(4552918929/10000000000 : ℝ)*X 0 1+(60273581/156250000 : ℝ)*X 0 2+(2097147563/5000000000 : ℝ)*X 1 0+(4552918929/10000000000 : ℝ)*X 1 1+(60273581/156250000 : ℝ)*X 1 2+(2097147563/5000000000 : ℝ)*X 2 0+(4552918929/10000000000 : ℝ)*X 2 1+(60273581/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27264839927989645803627929/6675000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (581777173/100000000000000 : ℝ)*(base19) + (266054993/50000000000000 : ℝ)*(base23) + (14364117/50000000000000 : ℝ)*(lower2) + (112356433/100000000000000 : ℝ)*(upper3) + (42423963/100000000000000 : ℝ)*(upper5) + (49950836861141/2000000000000 : ℝ)*(major0) + (49950836861141/2000000000000 : ℝ)*(major1) + (49950836861141/2000000000000 : ℝ)*(major2) + (1789753883955197/50000000000000 : ℝ)*(sp0) + (3579513588556493/100000000000000 : ℝ)*(sp1) + (11185980119449/312500000000 : ℝ)*(sp2) + (141556632389851/10000000000000 : ℝ)*(sp3) + (6402423273/100000000000000 : ℝ)*(sp4) + (611145581/20000000000000 : ℝ)*(sp7) + (707784689813207/50000000000000 : ℝ)*(f.failure) + (1789757085166833/50000000000000 : ℝ)*(f.sum) + (211561624931/200250000000000000000000000 : ℝ)*base65 + (226556007487732357/26700000000000000000000000000000 : ℝ)*base68 + (212774735657632357/26700000000000000000000000000000 : ℝ)*base70 + (107994561314332357/26700000000000000000000000000000 : ℝ)*base72 + (94584685933/32040000000000000000000000 : ℝ)*base74 + (68106550294432357/26700000000000000000000000000000 : ℝ)*base76 + (45497166140632357/26700000000000000000000000000000 : ℝ)*base78 + (44472810193867643/26700000000000000000000000000000 : ℝ)*base79 + (2179076890147/801000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (75541097/5000000000000000000000 : ℝ)*base90 + (75541097/5000000000000000000000 : ℝ)*base92 + (75541097/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (496795215504776959731671783/41718750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1472441217/100000000000000 : ℝ)*(base19) + (1970341/78125000000 : ℝ)*(base23) + (62513193/20000000000000 : ℝ)*(upper3) + (8355777/5000000000000 : ℝ)*(lower4) + (1679791/100000000000000 : ℝ)*(upper5) + (158570231086607/6250000000000 : ℝ)*(major0) + (158570231086607/6250000000000 : ℝ)*(major1) + (158570231086607/6250000000000 : ℝ)*(major2) + (222736073/1562500000000 : ℝ)*(sp1) + (21857995559/100000000000000 : ℝ)*(sp2) + (1818121607450357/50000000000000 : ℝ)*(sp4) + (1818113743675413/50000000000000 : ℝ)*(sp5) + (1818109417434337/50000000000000 : ℝ)*(sp6) + (1438003782930707/100000000000000 : ℝ)*(sp7) + (1438003782930707/100000000000000 : ℝ)*(f.failure) + (1818121607450357/50000000000000 : ℝ)*(f.sum) + (1999479490691/2503125000000000000000000000 : ℝ)*base65 + (548255804080842739/83437500000000000000000000000000 : ℝ)*base68 + (282633476793219761/83437500000000000000000000000000 : ℝ)*base69 + (251973580414280239/83437500000000000000000000000000 : ℝ)*base72 + (15200807975447/20025000000000000000000000000 : ℝ)*base74 + (461002542750530239/83437500000000000000000000000000 : ℝ)*base76 + (274663187452907261/83437500000000000000000000000000 : ℝ)*base77 + (71939275318655239/83437500000000000000000000000000 : ℝ)*base80 + (80548489544953/20025000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (15383597/10000000000000000000000 : ℝ)*base90 + (15383597/10000000000000000000000 : ℝ)*base92 + (15383597/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1632_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (176433729/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17507/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9497/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10477/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2051/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1632_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1632_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (176433729/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10477/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2051/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1632_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1632_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1632_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (176433729/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10477/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2051/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1632_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

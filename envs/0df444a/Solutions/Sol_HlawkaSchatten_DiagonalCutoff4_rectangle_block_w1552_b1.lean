-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1552_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:10:10.47997+00:00
-- url     : https://prove2.me/submissions/aaf3ea50-dd96-4a1d-ac1a-ed626a5702bc

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
theorem support_rectangle_w1552_s3_0 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-226274147/1250000000 : ℝ)*x 0 + (5430142763/10000000000 : ℝ)*x 1 + (5217553367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (226274147/1250000000 : ℝ)^4601 ≤ (693603571587/6250000000000 : ℝ)^3577 := by
    have hnat : (226274147 : ℕ)^4601*6250000000000^3577 ≤ 693603571587^3577*1250000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226274147 1250000000 693603571587 6250000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5430142763/10000000000 : ℝ)^4601 ≤ (2279632094567/5000000000000 : ℝ)^3577 := by
    have hnat : (5430142763 : ℕ)^4601*5000000000000^3577 ≤ 2279632094567^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430142763 10000000000 2279632094567 5000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217553367/10000000000 : ℝ)^4601 ≤ (21654850470831/50000000000000 : ℝ)^3577 := by
    have hnat : (5217553367 : ℕ)^4601*50000000000000^3577 ≤ 21654850470831^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217553367 10000000000 21654850470831 50000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-226274147/1250000000 : ℝ), (5430142763/10000000000 : ℝ), (5217553367/10000000000 : ℝ)] ![(693603571587/6250000000000 : ℝ), (2279632094567/5000000000000 : ℝ), (21654850470831/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-226274147/1250000000 : ℝ)|^4601 ≤ (693603571587/6250000000000 : ℝ)^3577
        have hw : |(-226274147/1250000000 : ℝ)|=(226274147/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5430142763/10000000000 : ℝ)|^4601 ≤ (2279632094567/5000000000000 : ℝ)^3577
        have hw : |(5430142763/10000000000 : ℝ)|=(5430142763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217553367/10000000000 : ℝ)|^4601 ≤ (21654850470831/50000000000000 : ℝ)^3577
        have hw : |(5217553367/10000000000 : ℝ)|=(5217553367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s3_1 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674912979/5000000000 : ℝ)*x 0 + (-479758377/2500000000 : ℝ)*x 1 + (1304388343/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674912979/5000000000 : ℝ)^4601 ≤ (4472707719441/10000000000000 : ℝ)^3577 := by
    have hnat : (2674912979 : ℕ)^4601*10000000000000^3577 ≤ 4472707719441^3577*5000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674912979 5000000000 4472707719441 10000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (479758377/2500000000 : ℝ)^4601 ≤ (11963221798717/100000000000000 : ℝ)^3577 := by
    have hnat : (479758377 : ℕ)^4601*100000000000000^3577 ≤ 11963221798717^3577*2500000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      479758377 2500000000 11963221798717 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304388343/2500000000 : ℝ)^4601 ≤ (43309700995047/100000000000000 : ℝ)^3577 := by
    have hnat : (1304388343 : ℕ)^4601*100000000000000^3577 ≤ 43309700995047^3577*2500000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304388343 2500000000 43309700995047 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674912979/5000000000 : ℝ), (-479758377/2500000000 : ℝ), (1304388343/2500000000 : ℝ)] ![(4472707719441/10000000000000 : ℝ), (11963221798717/100000000000000 : ℝ), (43309700995047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674912979/5000000000 : ℝ)|^4601 ≤ (4472707719441/10000000000000 : ℝ)^3577
        have hw : |(2674912979/5000000000 : ℝ)|=(2674912979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-479758377/2500000000 : ℝ)|^4601 ≤ (11963221798717/100000000000000 : ℝ)^3577
        have hw : |(-479758377/2500000000 : ℝ)|=(479758377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304388343/2500000000 : ℝ)|^4601 ≤ (43309700995047/100000000000000 : ℝ)^3577
        have hw : |(1304388343/2500000000 : ℝ)|=(1304388343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s3_2 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069965191/2000000000 : ℝ)*x 0 + (5217553369/10000000000 : ℝ)*x 1 + (-479758379/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069965191/2000000000 : ℝ)^4601 ≤ (11181769290537/25000000000000 : ℝ)^3577 := by
    have hnat : (1069965191 : ℕ)^4601*25000000000000^3577 ≤ 11181769290537^3577*2000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069965191 2000000000 11181769290537 25000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217553369/10000000000 : ℝ)^4601 ≤ (5413712620377/12500000000000 : ℝ)^3577 := by
    have hnat : (5217553369 : ℕ)^4601*12500000000000^3577 ≤ 5413712620377^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217553369 10000000000 5413712620377 12500000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (479758379/2500000000 : ℝ)^4601 ≤ (2392644372573/20000000000000 : ℝ)^3577 := by
    have hnat : (479758379 : ℕ)^4601*20000000000000^3577 ≤ 2392644372573^3577*2500000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      479758379 2500000000 2392644372573 20000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069965191/2000000000 : ℝ), (5217553369/10000000000 : ℝ), (-479758379/2500000000 : ℝ)] ![(11181769290537/25000000000000 : ℝ), (5413712620377/12500000000000 : ℝ), (2392644372573/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069965191/2000000000 : ℝ)|^4601 ≤ (11181769290537/25000000000000 : ℝ)^3577
        have hw : |(1069965191/2000000000 : ℝ)|=(1069965191/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217553369/10000000000 : ℝ)|^4601 ≤ (5413712620377/12500000000000 : ℝ)^3577
        have hw : |(5217553369/10000000000 : ℝ)|=(5217553369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-479758379/2500000000 : ℝ)|^4601 ≤ (2392644372573/20000000000000 : ℝ)^3577
        have hw : |(-479758379/2500000000 : ℝ)|=(479758379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s3_3 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062826523/2500000000 : ℝ)*x 0 + (4009400197/10000000000 : ℝ)*x 1 + (563135373/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062826523/2500000000 : ℝ)^4601 ≤ (4159951050511/12500000000000 : ℝ)^3577 := by
    have hnat : (1062826523 : ℕ)^4601*12500000000000^3577 ≤ 4159951050511^3577*2500000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062826523 2500000000 4159951050511 12500000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4009400197/10000000000 : ℝ)^4601 ≤ (3857994529189/12500000000000 : ℝ)^3577 := by
    have hnat : (4009400197 : ℕ)^4601*12500000000000^3577 ≤ 3857994529189^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4009400197 10000000000 3857994529189 12500000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (563135373/1250000000 : ℝ)^4601 ≤ (4482054418907/12500000000000 : ℝ)^3577 := by
    have hnat : (563135373 : ℕ)^4601*12500000000000^3577 ≤ 4482054418907^3577*1250000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563135373 1250000000 4482054418907 12500000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062826523/2500000000 : ℝ), (4009400197/10000000000 : ℝ), (563135373/1250000000 : ℝ)] ![(4159951050511/12500000000000 : ℝ), (3857994529189/12500000000000 : ℝ), (4482054418907/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062826523/2500000000 : ℝ)|^4601 ≤ (4159951050511/12500000000000 : ℝ)^3577
        have hw : |(1062826523/2500000000 : ℝ)|=(1062826523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4009400197/10000000000 : ℝ)|^4601 ≤ (3857994529189/12500000000000 : ℝ)^3577
        have hw : |(4009400197/10000000000 : ℝ)|=(4009400197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(563135373/1250000000 : ℝ)|^4601 ≤ (4482054418907/12500000000000 : ℝ)^3577
        have hw : |(563135373/1250000000 : ℝ)|=(563135373/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s3_4 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1810222251/10000000000 : ℝ)*x 0 + (208747083/400000000 : ℝ)*x 1 + (1357252633/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1810222251/10000000000 : ℝ)^4601 ≤ (11097886422341/100000000000000 : ℝ)^3577 := by
    have hnat : (1810222251 : ℕ)^4601*100000000000000^3577 ≤ 11097886422341^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1810222251 10000000000 11097886422341 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208747083/400000000 : ℝ)^4601 ≤ (43321699206341/100000000000000 : ℝ)^3577 := by
    have hnat : (208747083 : ℕ)^4601*100000000000000^3577 ≤ 43321699206341^3577*400000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208747083 400000000 43321699206341 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357252633/2500000000 : ℝ)^4601 ≤ (9116082871447/20000000000000 : ℝ)^3577 := by
    have hnat : (1357252633 : ℕ)^4601*20000000000000^3577 ≤ 9116082871447^3577*2500000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357252633 2500000000 9116082871447 20000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1810222251/10000000000 : ℝ), (208747083/400000000 : ℝ), (1357252633/2500000000 : ℝ)] ![(11097886422341/100000000000000 : ℝ), (43321699206341/100000000000000 : ℝ), (9116082871447/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1810222251/10000000000 : ℝ)|^4601 ≤ (11097886422341/100000000000000 : ℝ)^3577
        have hw : |(-1810222251/10000000000 : ℝ)|=(1810222251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(208747083/400000000 : ℝ)|^4601 ≤ (43321699206341/100000000000000 : ℝ)^3577
        have hw : |(208747083/400000000 : ℝ)|=(208747083/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357252633/2500000000 : ℝ)|^4601 ≤ (9116082871447/20000000000000 : ℝ)^3577
        have hw : |(1357252633/2500000000 : ℝ)|=(1357252633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s3_5 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323426417/2500000000 : ℝ)*x 0 + (-426894057/2500000000 : ℝ)*x 1 + (542901061/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323426417/2500000000 : ℝ)^4601 ≤ (2757779763227/6250000000000 : ℝ)^3577 := by
    have hnat : (1323426417 : ℕ)^4601*6250000000000^3577 ≤ 2757779763227^3577*2500000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323426417 2500000000 2757779763227 6250000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (426894057/2500000000 : ℝ)^4601 ≤ (10295108575051/100000000000000 : ℝ)^3577 := by
    have hnat : (426894057 : ℕ)^4601*100000000000000^3577 ≤ 10295108575051^3577*2500000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426894057 2500000000 10295108575051 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542901061/1000000000 : ℝ)^4601 ≤ (45580415199571/100000000000000 : ℝ)^3577 := by
    have hnat : (542901061 : ℕ)^4601*100000000000000^3577 ≤ 45580415199571^3577*1000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542901061 1000000000 45580415199571 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323426417/2500000000 : ℝ), (-426894057/2500000000 : ℝ), (542901061/1000000000 : ℝ)] ![(2757779763227/6250000000000 : ℝ), (10295108575051/100000000000000 : ℝ), (45580415199571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323426417/2500000000 : ℝ)|^4601 ≤ (2757779763227/6250000000000 : ℝ)^3577
        have hw : |(1323426417/2500000000 : ℝ)|=(1323426417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-426894057/2500000000 : ℝ)|^4601 ≤ (10295108575051/100000000000000 : ℝ)^3577
        have hw : |(-426894057/2500000000 : ℝ)|=(426894057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(542901061/1000000000 : ℝ)|^4601 ≤ (45580415199571/100000000000000 : ℝ)^3577
        have hw : |(542901061/1000000000 : ℝ)|=(542901061/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s3_6 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293705527/10000000000 : ℝ)*x 0 + (5429010627/10000000000 : ℝ)*x 1 + (-1707576399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293705527/10000000000 : ℝ)^4601 ≤ (4412447469991/10000000000000 : ℝ)^3577 := by
    have hnat : (5293705527 : ℕ)^4601*10000000000000^3577 ≤ 4412447469991^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293705527 10000000000 4412447469991 10000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5429010627/10000000000 : ℝ)^4601 ≤ (22790207691579/50000000000000 : ℝ)^3577 := by
    have hnat : (5429010627 : ℕ)^4601*50000000000000^3577 ≤ 22790207691579^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429010627 10000000000 22790207691579 50000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1707576399/10000000000 : ℝ)^4601 ≤ (10295109901163/100000000000000 : ℝ)^3577 := by
    have hnat : (1707576399 : ℕ)^4601*100000000000000^3577 ≤ 10295109901163^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1707576399 10000000000 10295109901163 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293705527/10000000000 : ℝ), (5429010627/10000000000 : ℝ), (-1707576399/10000000000 : ℝ)] ![(4412447469991/10000000000000 : ℝ), (22790207691579/50000000000000 : ℝ), (10295109901163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293705527/10000000000 : ℝ)|^4601 ≤ (4412447469991/10000000000000 : ℝ)^3577
        have hw : |(5293705527/10000000000 : ℝ)|=(5293705527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5429010627/10000000000 : ℝ)|^4601 ≤ (22790207691579/50000000000000 : ℝ)^3577
        have hw : |(5429010627/10000000000 : ℝ)|=(5429010627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1707576399/10000000000 : ℝ)|^4601 ≤ (10295109901163/100000000000000 : ℝ)^3577
        have hw : |(-1707576399/10000000000 : ℝ)|=(1707576399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s3_7 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42513737/100000000 : ℝ)*x 0 + (4502462679/10000000000 : ℝ)*x 1 + (1003010047/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42513737/100000000 : ℝ)^4601 ≤ (16640144577477/50000000000000 : ℝ)^3577 := by
    have hnat : (42513737 : ℕ)^4601*50000000000000^3577 ≤ 16640144577477^3577*100000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42513737 100000000 16640144577477 50000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4502462679/10000000000 : ℝ)^4601 ≤ (35829611984181/100000000000000 : ℝ)^3577 := by
    have hnat : (4502462679 : ℕ)^4601*100000000000000^3577 ≤ 35829611984181^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502462679 10000000000 35829611984181 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1003010047/2500000000 : ℝ)^4601 ≤ (30890098837833/100000000000000 : ℝ)^3577 := by
    have hnat : (1003010047 : ℕ)^4601*100000000000000^3577 ≤ 30890098837833^3577*2500000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003010047 2500000000 30890098837833 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42513737/100000000 : ℝ), (4502462679/10000000000 : ℝ), (1003010047/2500000000 : ℝ)] ![(16640144577477/50000000000000 : ℝ), (35829611984181/100000000000000 : ℝ), (30890098837833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42513737/100000000 : ℝ)|^4601 ≤ (16640144577477/50000000000000 : ℝ)^3577
        have hw : |(42513737/100000000 : ℝ)|=(42513737/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4502462679/10000000000 : ℝ)|^4601 ≤ (35829611984181/100000000000000 : ℝ)^3577
        have hw : |(4502462679/10000000000 : ℝ)|=(4502462679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1003010047/2500000000 : ℝ)|^4601 ≤ (30890098837833/100000000000000 : ℝ)^3577
        have hw : |(1003010047/2500000000 : ℝ)|=(1003010047/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1552_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83291099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7931/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5357/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5511/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1941/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7931/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5357/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7931/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5357/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7931/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5357/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7931/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5357/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7931/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5357/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7931/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5357/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5357/50000 : ℝ) ^ (4599/1024 : ℝ) ≤ (87970730936103/2000000000000000000 : ℝ) := by
    have hpowers : (5357/50000 : ℝ)^4599 ≤ (87970730936103/2000000000000000000 : ℝ)^1024 := by
      have hnat : (5357 : ℕ)^4599*2000000000000000000^1024 ≤ 87970730936103^1024*50000^4599 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5357 50000 87970730936103 2000000000000000000 4599 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5357/50000 : ℝ)) (X := (87970730936103/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4599 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7931/50000 : ℝ) ^ (4599/1024 : ℝ) ≤ (25623524056076211/100000000000000000000 : ℝ) := by
    have hpowers : (7931/50000 : ℝ)^4599 ≤ (25623524056076211/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7931 : ℕ)^4599*100000000000000000000^1024 ≤ 25623524056076211^1024*50000^4599 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7931 50000 25623524056076211 100000000000000000000 4599 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7931/50000 : ℝ)) (X := (25623524056076211/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4599 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000087970730936103/1000000000000000000 : ℝ) ≤ (1000019586638091/1000000000000000 : ℝ) ^ (4599/1024 : ℝ) := by
    have hpowers : (1000087970730936103/1000000000000000000 : ℝ)^1024 ≤ (1000019586638091/1000000000000000 : ℝ)^4599 := by
      have hnat : (1000087970730936103 : ℕ)^1024*1000000000000000^4599 ≤ 1000019586638091^4599*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000087970730936103 1000000000000000000 1000019586638091 1000000000000000 1024 4599 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000019586638091/1000000000000000 : ℝ)) (X := (1000087970730936103/1000000000000000000 : ℝ)) (by norm_num) 4599 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100030022060602881361/100000000000000000000 : ℝ) ≤ (5000334192252981/5000000000000000 : ℝ) ^ (4599/1024 : ℝ) := by
    have hpowers : (100030022060602881361/100000000000000000000 : ℝ)^1024 ≤ (5000334192252981/5000000000000000 : ℝ)^4599 := by
      have hnat : (100030022060602881361 : ℕ)^1024*5000000000000000^4599 ≤ 5000334192252981^4599*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100030022060602881361 100000000000000000000 5000334192252981 5000000000000000 1024 4599 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000334192252981/5000000000000000 : ℝ)) (X := (100030022060602881361/100000000000000000000 : ℝ)) (by norm_num) 4599 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50025623524056076211/50000000000000000000 : ℝ) ≤ (5000570451315507/5000000000000000 : ℝ) ^ (4599/1024 : ℝ) := by
    have hpowers : (50025623524056076211/50000000000000000000 : ℝ)^1024 ≤ (5000570451315507/5000000000000000 : ℝ)^4599 := by
      have hnat : (50025623524056076211 : ℕ)^1024*5000000000000000^4599 ≤ 5000570451315507^4599*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025623524056076211 50000000000000000000 5000570451315507 5000000000000000 1024 4599 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000570451315507/5000000000000000 : ℝ)) (X := (50025623524056076211/50000000000000000000 : ℝ)) (by norm_num) 4599 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(87970730936103/2000000000000000000 : ℝ) ≤ ((194965466673277691/195000000000000000 : ℝ)+2*(39376510421/42900000000000 : ℝ)*(5357/50000 : ℝ))^(4599/1024 : ℝ) := by
    rw [show (194965466673277691/195000000000000000 : ℝ)+2*(39376510421/42900000000000 : ℝ)*(5357/50000 : ℝ)=(1000019586638091/1000000000000000 : ℝ) by norm_num, show 1+2*(87970730936103/2000000000000000000 : ℝ)=(1000087970730936103/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(25623524056076211/100000000000000000000 : ℝ)+(87970730936103/2000000000000000000 : ℝ) ≤ ((194965466673277691/195000000000000000 : ℝ)+(39376510421/42900000000000 : ℝ)*((7931/50000 : ℝ)+(5357/50000 : ℝ)))^(4599/1024 : ℝ) := by
    rw [show (194965466673277691/195000000000000000 : ℝ)+(39376510421/42900000000000 : ℝ)*((7931/50000 : ℝ)+(5357/50000 : ℝ))=(5000334192252981/5000000000000000 : ℝ) by norm_num, show 1+(25623524056076211/100000000000000000000 : ℝ)+(87970730936103/2000000000000000000 : ℝ)=(100030022060602881361/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(25623524056076211/100000000000000000000 : ℝ) ≤ ((194965466673277691/195000000000000000 : ℝ)+2*(39376510421/42900000000000 : ℝ)*(7931/50000 : ℝ))^(4599/1024 : ℝ) := by
    rw [show (194965466673277691/195000000000000000 : ℝ)+2*(39376510421/42900000000000 : ℝ)*(7931/50000 : ℝ)=(5000570451315507/5000000000000000 : ℝ) by norm_num, show 1+2*(25623524056076211/100000000000000000000 : ℝ)=(50025623524056076211/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (194965466673277691/195000000000000000 : ℝ)*(X 1 0+X 2 0)+(39376510421/42900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4599/1024 : ℝ)) (lo := (5357/50000 : ℝ)) (hi := (7931/50000 : ℝ)) (c := (194965466673277691/195000000000000000 : ℝ)) (alpha := (39376510421/42900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (194965466673277691/195000000000000000 : ℝ)*(X 0 1+X 2 1)+(39376510421/42900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4599/1024 : ℝ)) (lo := (5357/50000 : ℝ)) (hi := (7931/50000 : ℝ)) (c := (194965466673277691/195000000000000000 : ℝ)) (alpha := (39376510421/42900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (194965466673277691/195000000000000000 : ℝ)*(X 0 2+X 1 2)+(39376510421/42900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4599/1024 : ℝ)) (lo := (5357/50000 : ℝ)) (hi := (7931/50000 : ℝ)) (c := (194965466673277691/195000000000000000 : ℝ)) (alpha := (39376510421/42900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-226274147/1250000000 : ℝ)*X 0 0+(5430142763/10000000000 : ℝ)*X 0 1+(5217553367/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674912979/5000000000 : ℝ)*X 1 0+(-479758377/2500000000 : ℝ)*X 1 1+(1304388343/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069965191/2000000000 : ℝ)*X 2 0+(5217553369/10000000000 : ℝ)*X 2 1+(-479758379/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1062826523/2500000000 : ℝ)*X 0 0+(4009400197/10000000000 : ℝ)*X 0 1+(563135373/1250000000 : ℝ)*X 0 2+(1062826523/2500000000 : ℝ)*X 1 0+(4009400197/10000000000 : ℝ)*X 1 1+(563135373/1250000000 : ℝ)*X 1 2+(1062826523/2500000000 : ℝ)*X 2 0+(4009400197/10000000000 : ℝ)*X 2 1+(563135373/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1810222251/10000000000 : ℝ)*X 0 0+(208747083/400000000 : ℝ)*X 0 1+(1357252633/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323426417/2500000000 : ℝ)*X 1 0+(-426894057/2500000000 : ℝ)*X 1 1+(542901061/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293705527/10000000000 : ℝ)*X 2 0+(5429010627/10000000000 : ℝ)*X 2 1+(-1707576399/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((42513737/100000000 : ℝ)*X 0 0+(4502462679/10000000000 : ℝ)*X 0 1+(1003010047/2500000000 : ℝ)*X 0 2+(42513737/100000000 : ℝ)*X 1 0+(4502462679/10000000000 : ℝ)*X 1 1+(1003010047/2500000000 : ℝ)*X 1 2+(42513737/100000000 : ℝ)*X 2 0+(4502462679/10000000000 : ℝ)*X 2 1+(1003010047/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (58715707483563085165380487/17875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (277004363/50000000000000 : ℝ)*(base19) + (100316927/20000000000000 : ℝ)*(base23) + (66587/250000000000 : ℝ)*(lower2) + (10953963/12500000000000 : ℝ)*(upper3) + (862369/2000000000000 : ℝ)*(upper5) + (1680337071060287/50000000000000 : ℝ)*(major0) + (1680337071060287/50000000000000 : ℝ)*(major1) + (1680337071060287/50000000000000 : ℝ)*(major2) + (1175978184110737/25000000000000 : ℝ)*(sp0) + (293995042455241/6250000000000 : ℝ)*(sp1) + (4703920731707947/100000000000000 : ℝ)*(sp2) + (201742276765451/10000000000000 : ℝ)*(sp3) + (8496849633/100000000000000 : ℝ)*(sp4) + (521725111/12500000000000 : ℝ)*(sp7) + (2017426941455397/100000000000000 : ℝ)*(f.failure) + (2351960616646291/50000000000000 : ℝ)*(f.sum) + (11446923075751/2145000000000000000000000000 : ℝ)*base66 + (37721435013551501/8250000000000000000000000000000 : ℝ)*base68 + (5772241297698499/8250000000000000000000000000000 : ℝ)*base69 + (18871903876301501/8250000000000000000000000000000 : ℝ)*base72 + (1741390809947/268125000000000000000000000 : ℝ)*base74 + (4948711777698499/8250000000000000000000000000000 : ℝ)*base75 + (24327054156551501/8250000000000000000000000000000 : ℝ)*base78 + (71464550826551501/8250000000000000000000000000000 : ℝ)*base80 + (6354069383243/1072500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (24388697/5000000000000000000000 : ℝ)*base90 + (24388697/5000000000000000000000 : ℝ)*base92 + (24388697/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (780785455279553052097433/101562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (42409569/3125000000000 : ℝ)*(base19) + (1209677851/100000000000000 : ℝ)*(base23) + (80847837/50000000000000 : ℝ)*(upper3) + (15641867/100000000000000 : ℝ)*(lower4) + (100680629/50000000000000 : ℝ)*(upper5) + (26536768820647/781250000000 : ℝ)*(major0) + (26536768820647/781250000000 : ℝ)*(major1) + (26536768820647/781250000000 : ℝ)*(major2) + (11721521357/50000000000000 : ℝ)*(sp1) + (18694320717/100000000000000 : ℝ)*(sp2) + (4754355297712007/100000000000000 : ℝ)*(sp4) + (950866099512617/20000000000000 : ℝ)*(sp5) + (4754335393713439/100000000000000 : ℝ)*(sp6) + (2039057264115831/100000000000000 : ℝ)*(sp7) + (2039057264115831/100000000000000 : ℝ)*(f.failure) + (4754355297712007/100000000000000 : ℝ)*(f.sum) + (3656467642801/2145000000000000000000000000 : ℝ)*base65 + (1445777824154563/257812500000000000000000000000 : ℝ)*base67 + (158077435086781/128906250000000000000000000000 : ℝ)*base70 + (54403339454207/16113281250000000000000000000 : ℝ)*base72 + (7330444633771/2145000000000000000000000000 : ℝ)*base73 + (2655338964029563/257812500000000000000000000000 : ℝ)*base75 + (2042805656791/8056640625000000000000000000 : ℝ)*base78 + (506630850643999/515625000000000000000000000000 : ℝ)*base80 + (6793033173239/2145000000000000000000000000 : ℝ)*base82 + (27288269/5000000000000000000000 : ℝ)*base89 + (27288269/5000000000000000000000 : ℝ)*base91 + (27288269/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1552_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83291099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7931/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5357/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5511/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1941/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1552_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1552_s4_0 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-9052351/50000000 : ℝ)*x 0 + (5428295187/10000000000 : ℝ)*x 1 + (5219217417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9052351/50000000 : ℝ)^4601 ≤ (11099841718493/100000000000000 : ℝ)^3577 := by
    have hnat : (9052351 : ℕ)^4601*100000000000000^3577 ≤ 11099841718493^3577*50000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9052351 50000000 11099841718493 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428295187/10000000000 : ℝ)^4601 ≤ (2278634468089/5000000000000 : ℝ)^3577 := by
    have hnat : (5428295187 : ℕ)^4601*5000000000000^3577 ≤ 2278634468089^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428295187 10000000000 2278634468089 5000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219217417/10000000000 : ℝ)^4601 ≤ (43327468910081/100000000000000 : ℝ)^3577 := by
    have hnat : (5219217417 : ℕ)^4601*100000000000000^3577 ≤ 43327468910081^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219217417 10000000000 43327468910081 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-9052351/50000000 : ℝ), (5428295187/10000000000 : ℝ), (5219217417/10000000000 : ℝ)] ![(11099841718493/100000000000000 : ℝ), (2278634468089/5000000000000 : ℝ), (43327468910081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-9052351/50000000 : ℝ)|^4601 ≤ (11099841718493/100000000000000 : ℝ)^3577
        have hw : |(-9052351/50000000 : ℝ)|=(9052351/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428295187/10000000000 : ℝ)|^4601 ≤ (2278634468089/5000000000000 : ℝ)^3577
        have hw : |(5428295187/10000000000 : ℝ)|=(5428295187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219217417/10000000000 : ℝ)|^4601 ≤ (43327468910081/100000000000000 : ℝ)^3577
        have hw : |(5219217417/10000000000 : ℝ)|=(5219217417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s4_1 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (83583413/156250000 : ℝ)*x 0 + (-191747059/1000000000 : ℝ)*x 1 + (1304804489/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83583413/156250000 : ℝ)^4601 ≤ (44721834479101/100000000000000 : ℝ)^3577 := by
    have hnat : (83583413 : ℕ)^4601*100000000000000^3577 ≤ 44721834479101^3577*156250000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83583413 156250000 44721834479101 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (191747059/1000000000 : ℝ)^4601 ≤ (5975345417937/50000000000000 : ℝ)^3577 := by
    have hnat : (191747059 : ℕ)^4601*50000000000000^3577 ≤ 5975345417937^3577*1000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191747059 1000000000 5975345417937 50000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304804489/2500000000 : ℝ)^4601 ≤ (43327474665541/100000000000000 : ℝ)^3577 := by
    have hnat : (1304804489 : ℕ)^4601*100000000000000^3577 ≤ 43327474665541^3577*2500000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304804489 2500000000 43327474665541 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83583413/156250000 : ℝ), (-191747059/1000000000 : ℝ), (1304804489/2500000000 : ℝ)] ![(44721834479101/100000000000000 : ℝ), (5975345417937/50000000000000 : ℝ), (43327474665541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83583413/156250000 : ℝ)|^4601 ≤ (44721834479101/100000000000000 : ℝ)^3577
        have hw : |(83583413/156250000 : ℝ)|=(83583413/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-191747059/1000000000 : ℝ)|^4601 ≤ (5975345417937/50000000000000 : ℝ)^3577
        have hw : |(-191747059/1000000000 : ℝ)|=(191747059/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304804489/2500000000 : ℝ)|^4601 ≤ (43327474665541/100000000000000 : ℝ)^3577
        have hw : |(1304804489/2500000000 : ℝ)|=(1304804489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s4_2 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668667269/1250000000 : ℝ)*x 0 + (1304804527/2500000000 : ℝ)*x 1 + (-479367691/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668667269/1250000000 : ℝ)^4601 ≤ (44721831468101/100000000000000 : ℝ)^3577 := by
    have hnat : (668667269 : ℕ)^4601*100000000000000^3577 ≤ 44721831468101^3577*1250000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668667269 1250000000 44721831468101 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304804527/2500000000 : ℝ)^4601 ≤ (21663738144301/50000000000000 : ℝ)^3577 := by
    have hnat : (1304804527 : ℕ)^4601*50000000000000^3577 ≤ 21663738144301^3577*2500000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304804527 2500000000 21663738144301 50000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (479367691/2500000000 : ℝ)^4601 ≤ (5975346115393/50000000000000 : ℝ)^3577 := by
    have hnat : (479367691 : ℕ)^4601*50000000000000^3577 ≤ 5975346115393^3577*2500000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      479367691 2500000000 5975346115393 50000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668667269/1250000000 : ℝ), (1304804527/2500000000 : ℝ), (-479367691/2500000000 : ℝ)] ![(44721831468101/100000000000000 : ℝ), (21663738144301/50000000000000 : ℝ), (5975346115393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668667269/1250000000 : ℝ)|^4601 ≤ (44721831468101/100000000000000 : ℝ)^3577
        have hw : |(668667269/1250000000 : ℝ)|=(668667269/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304804527/2500000000 : ℝ)|^4601 ≤ (21663738144301/50000000000000 : ℝ)^3577
        have hw : |(1304804527/2500000000 : ℝ)|=(1304804527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-479367691/2500000000 : ℝ)|^4601 ≤ (5975346115393/50000000000000 : ℝ)^3577
        have hw : |(-479367691/2500000000 : ℝ)|=(479367691/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s4_3 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2125740391/5000000000 : ℝ)*x 0 + (4013475731/10000000000 : ℝ)*x 1 + (4500968277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2125740391/5000000000 : ℝ)^4601 ≤ (33281367379321/100000000000000 : ℝ)^3577 := by
    have hnat : (2125740391 : ℕ)^4601*100000000000000^3577 ≤ 33281367379321^3577*5000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125740391 5000000000 33281367379321 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4013475731/10000000000 : ℝ)^4601 ≤ (30904316420509/100000000000000 : ℝ)^3577 := by
    have hnat : (4013475731 : ℕ)^4601*100000000000000^3577 ≤ 30904316420509^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4013475731 10000000000 30904316420509 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4500968277/10000000000 : ℝ)^4601 ≤ (3581431618821/10000000000000 : ℝ)^3577 := by
    have hnat : (4500968277 : ℕ)^4601*10000000000000^3577 ≤ 3581431618821^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500968277 10000000000 3581431618821 10000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2125740391/5000000000 : ℝ), (4013475731/10000000000 : ℝ), (4500968277/10000000000 : ℝ)] ![(33281367379321/100000000000000 : ℝ), (30904316420509/100000000000000 : ℝ), (3581431618821/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2125740391/5000000000 : ℝ)|^4601 ≤ (33281367379321/100000000000000 : ℝ)^3577
        have hw : |(2125740391/5000000000 : ℝ)|=(2125740391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4013475731/10000000000 : ℝ)|^4601 ≤ (30904316420509/100000000000000 : ℝ)^3577
        have hw : |(4013475731/10000000000 : ℝ)|=(4013475731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4500968277/10000000000 : ℝ)|^4601 ≤ (3581431618821/10000000000000 : ℝ)^3577
        have hw : |(4500968277/10000000000 : ℝ)|=(4500968277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s4_4 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-226312177/1250000000 : ℝ)*x 0 + (652538131/1250000000 : ℝ)*x 1 + (5427199777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (226312177/1250000000 : ℝ)^4601 ≤ (5550028172641/50000000000000 : ℝ)^3577 := by
    have hnat : (226312177 : ℕ)^4601*50000000000000^3577 ≤ 5550028172641^3577*1250000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226312177 1250000000 5550028172641 50000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (652538131/1250000000 : ℝ)^4601 ≤ (21669541507629/50000000000000 : ℝ)^3577 := by
    have hnat : (652538131 : ℕ)^4601*50000000000000^3577 ≤ 21669541507629^3577*1250000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652538131 1250000000 21669541507629 50000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5427199777/10000000000 : ℝ)^4601 ≤ (142377689429/312500000000 : ℝ)^3577 := by
    have hnat : (5427199777 : ℕ)^4601*312500000000^3577 ≤ 142377689429^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427199777 10000000000 142377689429 312500000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-226312177/1250000000 : ℝ), (652538131/1250000000 : ℝ), (5427199777/10000000000 : ℝ)] ![(5550028172641/50000000000000 : ℝ), (21669541507629/50000000000000 : ℝ), (142377689429/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-226312177/1250000000 : ℝ)|^4601 ≤ (5550028172641/50000000000000 : ℝ)^3577
        have hw : |(-226312177/1250000000 : ℝ)|=(226312177/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(652538131/1250000000 : ℝ)|^4601 ≤ (21669541507629/50000000000000 : ℝ)^3577
        have hw : |(652538131/1250000000 : ℝ)|=(652538131/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5427199777/10000000000 : ℝ)|^4601 ≤ (142377689429/312500000000 : ℝ)^3577
        have hw : |(5427199777/10000000000 : ℝ)|=(5427199777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s4_5 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323536461/2500000000 : ℝ)*x 0 + (-1709488843/10000000000 : ℝ)*x 1 + (678399977/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323536461/2500000000 : ℝ)^4601 ≤ (44129195587787/100000000000000 : ℝ)^3577 := by
    have hnat : (1323536461 : ℕ)^4601*100000000000000^3577 ≤ 44129195587787^3577*2500000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323536461 2500000000 44129195587787 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1709488843/10000000000 : ℝ)^4601 ≤ (2577485840259/25000000000000 : ℝ)^3577 := by
    have hnat : (1709488843 : ℕ)^4601*25000000000000^3577 ≤ 2577485840259^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1709488843 10000000000 2577485840259 25000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (678399977/1250000000 : ℝ)^4601 ≤ (5695107629801/12500000000000 : ℝ)^3577 := by
    have hnat : (678399977 : ℕ)^4601*12500000000000^3577 ≤ 5695107629801^3577*1250000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678399977 1250000000 5695107629801 12500000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323536461/2500000000 : ℝ), (-1709488843/10000000000 : ℝ), (678399977/1250000000 : ℝ)] ![(44129195587787/100000000000000 : ℝ), (2577485840259/25000000000000 : ℝ), (5695107629801/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323536461/2500000000 : ℝ)|^4601 ≤ (44129195587787/100000000000000 : ℝ)^3577
        have hw : |(1323536461/2500000000 : ℝ)|=(1323536461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1709488843/10000000000 : ℝ)|^4601 ≤ (2577485840259/25000000000000 : ℝ)^3577
        have hw : |(-1709488843/10000000000 : ℝ)|=(1709488843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(678399977/1250000000 : ℝ)|^4601 ≤ (5695107629801/12500000000000 : ℝ)^3577
        have hw : |(678399977/1250000000 : ℝ)|=(678399977/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s4_6 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294145859/10000000000 : ℝ)*x 0 + (1085439967/2000000000 : ℝ)*x 1 + (-341897759/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294145859/10000000000 : ℝ)^4601 ≤ (11032298937153/25000000000000 : ℝ)^3577 := by
    have hnat : (5294145859 : ℕ)^4601*25000000000000^3577 ≤ 11032298937153^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294145859 10000000000 11032298937153 25000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085439967/2000000000 : ℝ)^4601 ≤ (45560861243573/100000000000000 : ℝ)^3577 := by
    have hnat : (1085439967 : ℕ)^4601*100000000000000^3577 ≤ 45560861243573^3577*2000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085439967 2000000000 45560861243573 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (341897759/2000000000 : ℝ)^4601 ≤ (412397719547/4000000000000 : ℝ)^3577 := by
    have hnat : (341897759 : ℕ)^4601*4000000000000^3577 ≤ 412397719547^3577*2000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341897759 2000000000 412397719547 4000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294145859/10000000000 : ℝ), (1085439967/2000000000 : ℝ), (-341897759/2000000000 : ℝ)] ![(11032298937153/25000000000000 : ℝ), (45560861243573/100000000000000 : ℝ), (412397719547/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294145859/10000000000 : ℝ)|^4601 ≤ (11032298937153/25000000000000 : ℝ)^3577
        have hw : |(5294145859/10000000000 : ℝ)|=(5294145859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1085439967/2000000000 : ℝ)|^4601 ≤ (45560861243573/100000000000000 : ℝ)^3577
        have hw : |(1085439967/2000000000 : ℝ)|=(1085439967/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-341897759/2000000000 : ℝ)|^4601 ≤ (412397719547/4000000000000 : ℝ)^3577
        have hw : |(-341897759/2000000000 : ℝ)|=(341897759/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s4_7 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4251545097/10000000000 : ℝ)*x 0 + (224921691/500000000 : ℝ)*x 1 + (251001807/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4251545097/10000000000 : ℝ)^4601 ≤ (8320503745057/25000000000000 : ℝ)^3577 := by
    have hnat : (4251545097 : ℕ)^4601*25000000000000^3577 ≤ 8320503745057^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251545097 10000000000 8320503745057 25000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (224921691/500000000 : ℝ)^4601 ≤ (7157675668267/20000000000000 : ℝ)^3577 := by
    have hnat : (224921691 : ℕ)^4601*20000000000000^3577 ≤ 7157675668267^3577*500000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224921691 500000000 7157675668267 20000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (251001807/625000000 : ℝ)^4601 ≤ (6185921331921/20000000000000 : ℝ)^3577 := by
    have hnat : (251001807 : ℕ)^4601*20000000000000^3577 ≤ 6185921331921^3577*625000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251001807 625000000 6185921331921 20000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4251545097/10000000000 : ℝ), (224921691/500000000 : ℝ), (251001807/625000000 : ℝ)] ![(8320503745057/25000000000000 : ℝ), (7157675668267/20000000000000 : ℝ), (6185921331921/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4251545097/10000000000 : ℝ)|^4601 ≤ (8320503745057/25000000000000 : ℝ)^3577
        have hw : |(4251545097/10000000000 : ℝ)|=(4251545097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(224921691/500000000 : ℝ)|^4601 ≤ (7157675668267/20000000000000 : ℝ)^3577
        have hw : |(224921691/500000000 : ℝ)|=(224921691/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(251001807/625000000 : ℝ)|^4601 ≤ (6185921331921/20000000000000 : ℝ)^3577
        have hw : |(251001807/625000000 : ℝ)|=(251001807/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1552_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83291099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1941/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5511/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11057/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15489/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1941/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5511/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1941/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5511/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1941/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5511/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1941/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5511/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1941/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5511/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1941/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5511/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5511/50000 : ℝ) ^ (4599/1024 : ℝ) ≤ (499562077768353/10000000000000000000 : ℝ) := by
    have hpowers : (5511/50000 : ℝ)^4599 ≤ (499562077768353/10000000000000000000 : ℝ)^1024 := by
      have hnat : (5511 : ℕ)^4599*10000000000000000000^1024 ≤ 499562077768353^1024*50000^4599 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5511 50000 499562077768353 10000000000000000000 4599 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5511/50000 : ℝ)) (X := (499562077768353/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4599 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1941/12500 : ℝ) ^ (4599/1024 : ℝ) ≤ (18630271070679/80000000000000000 : ℝ) := by
    have hpowers : (1941/12500 : ℝ)^4599 ≤ (18630271070679/80000000000000000 : ℝ)^1024 := by
      have hnat : (1941 : ℕ)^4599*80000000000000000^1024 ≤ 18630271070679^1024*12500^4599 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1941 12500 18630271070679 80000000000000000 4599 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1941/12500 : ℝ)) (X := (18630271070679/80000000000000000 : ℝ)) (by norm_num) (by norm_num) 4599 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000499562077768353/5000000000000000000 : ℝ) ≤ (1250027806681/1250000000000 : ℝ) ^ (4599/1024 : ℝ) := by
    have hpowers : (5000499562077768353/5000000000000000000 : ℝ)^1024 ≤ (1250027806681/1250000000000 : ℝ)^4599 := by
      have hnat : (5000499562077768353 : ℕ)^1024*1250000000000^4599 ≤ 1250027806681^4599*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000499562077768353 5000000000000000000 1250027806681 1250000000000 1024 4599 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250027806681/1250000000000 : ℝ)) (X := (5000499562077768353/5000000000000000000 : ℝ)) (by norm_num) 4599 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2500707086490400807/2500000000000000000 : ℝ) ≤ (10000629682091029/10000000000000000 : ℝ) ^ (4599/1024 : ℝ) := by
    have hpowers : (2500707086490400807/2500000000000000000 : ℝ)^1024 ≤ (10000629682091029/10000000000000000 : ℝ)^4599 := by
      have hnat : (2500707086490400807 : ℕ)^1024*10000000000000000^4599 ≤ 10000629682091029^4599*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500707086490400807 2500000000000000000 10000629682091029 10000000000000000 1024 4599 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000629682091029/10000000000000000 : ℝ)) (X := (2500707086490400807/2500000000000000000 : ℝ)) (by norm_num) 4599 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (40018630271070679/40000000000000000 : ℝ) ≤ (5000518455367029/5000000000000000 : ℝ) ^ (4599/1024 : ℝ) := by
    have hpowers : (40018630271070679/40000000000000000 : ℝ)^1024 ≤ (5000518455367029/5000000000000000 : ℝ)^4599 := by
      have hnat : (40018630271070679 : ℕ)^1024*5000000000000000^4599 ≤ 5000518455367029^4599*40000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40018630271070679 40000000000000000 5000518455367029 5000000000000000 1024 4599 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000518455367029/5000000000000000 : ℝ)) (X := (40018630271070679/40000000000000000 : ℝ)) (by norm_num) 4599 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(499562077768353/10000000000000000000 : ℝ) ≤ ((3754335452252479727/3755000000000000000 : ℝ)+2*(407228643029/450600000000000 : ℝ)*(5511/50000 : ℝ))^(4599/1024 : ℝ) := by
    rw [show (3754335452252479727/3755000000000000000 : ℝ)+2*(407228643029/450600000000000 : ℝ)*(5511/50000 : ℝ)=(1250027806681/1250000000000 : ℝ) by norm_num, show 1+2*(499562077768353/10000000000000000000 : ℝ)=(5000499562077768353/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18630271070679/80000000000000000 : ℝ)+(499562077768353/10000000000000000000 : ℝ) ≤ ((3754335452252479727/3755000000000000000 : ℝ)+(407228643029/450600000000000 : ℝ)*((1941/12500 : ℝ)+(5511/50000 : ℝ)))^(4599/1024 : ℝ) := by
    rw [show (3754335452252479727/3755000000000000000 : ℝ)+(407228643029/450600000000000 : ℝ)*((1941/12500 : ℝ)+(5511/50000 : ℝ))=(10000629682091029/10000000000000000 : ℝ) by norm_num, show 1+(18630271070679/80000000000000000 : ℝ)+(499562077768353/10000000000000000000 : ℝ)=(2500707086490400807/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18630271070679/80000000000000000 : ℝ) ≤ ((3754335452252479727/3755000000000000000 : ℝ)+2*(407228643029/450600000000000 : ℝ)*(1941/12500 : ℝ))^(4599/1024 : ℝ) := by
    rw [show (3754335452252479727/3755000000000000000 : ℝ)+2*(407228643029/450600000000000 : ℝ)*(1941/12500 : ℝ)=(5000518455367029/5000000000000000 : ℝ) by norm_num, show 1+2*(18630271070679/80000000000000000 : ℝ)=(40018630271070679/40000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3754335452252479727/3755000000000000000 : ℝ)*(X 1 0+X 2 0)+(407228643029/450600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4599/1024 : ℝ)) (lo := (5511/50000 : ℝ)) (hi := (1941/12500 : ℝ)) (c := (3754335452252479727/3755000000000000000 : ℝ)) (alpha := (407228643029/450600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3754335452252479727/3755000000000000000 : ℝ)*(X 0 1+X 2 1)+(407228643029/450600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4599/1024 : ℝ)) (lo := (5511/50000 : ℝ)) (hi := (1941/12500 : ℝ)) (c := (3754335452252479727/3755000000000000000 : ℝ)) (alpha := (407228643029/450600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3754335452252479727/3755000000000000000 : ℝ)*(X 0 2+X 1 2)+(407228643029/450600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4599/1024 : ℝ)) (lo := (5511/50000 : ℝ)) (hi := (1941/12500 : ℝ)) (c := (3754335452252479727/3755000000000000000 : ℝ)) (alpha := (407228643029/450600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-9052351/50000000 : ℝ)*X 0 0+(5428295187/10000000000 : ℝ)*X 0 1+(5219217417/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((83583413/156250000 : ℝ)*X 1 0+(-191747059/1000000000 : ℝ)*X 1 1+(1304804489/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668667269/1250000000 : ℝ)*X 2 0+(1304804527/2500000000 : ℝ)*X 2 1+(-479367691/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2125740391/5000000000 : ℝ)*X 0 0+(4013475731/10000000000 : ℝ)*X 0 1+(4500968277/10000000000 : ℝ)*X 0 2+(2125740391/5000000000 : ℝ)*X 1 0+(4013475731/10000000000 : ℝ)*X 1 1+(4500968277/10000000000 : ℝ)*X 1 2+(2125740391/5000000000 : ℝ)*X 2 0+(4013475731/10000000000 : ℝ)*X 2 1+(4500968277/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-226312177/1250000000 : ℝ)*X 0 0+(652538131/1250000000 : ℝ)*X 0 1+(5427199777/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323536461/2500000000 : ℝ)*X 1 0+(-1709488843/10000000000 : ℝ)*X 1 1+(678399977/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294145859/10000000000 : ℝ)*X 2 0+(1085439967/2000000000 : ℝ)*X 2 1+(-341897759/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4251545097/10000000000 : ℝ)*X 0 0+(224921691/500000000 : ℝ)*X 0 1+(251001807/625000000 : ℝ)*X 0 2+(4251545097/10000000000 : ℝ)*X 1 0+(224921691/500000000 : ℝ)*X 1 1+(251001807/625000000 : ℝ)*X 1 2+(4251545097/10000000000 : ℝ)*X 2 0+(224921691/500000000 : ℝ)*X 2 1+(251001807/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (72669270336258704904567/7510000000000000000000000000 : ℝ) := by norm_num
    linear_combination (248651487/12500000000000 : ℝ)*(base19) + (1550805239/100000000000000 : ℝ)*(base23) + (90134647/20000000000000 : ℝ)*(upper3) + (50297419/50000000000000 : ℝ)*(upper4) + (21814241/20000000000000 : ℝ)*(upper5) + (3417165377806861/100000000000000 : ℝ)*(major0) + (3417165377806861/100000000000000 : ℝ)*(major1) + (3417165377806861/100000000000000 : ℝ)*(major2) + (4782955111635459/100000000000000 : ℝ)*(sp0) + (191319582960717/4000000000000 : ℝ)*(sp1) + (4782990012424583/100000000000000 : ℝ)*(sp2) + (128207767444141/6250000000000 : ℝ)*(sp3) + (18225797181/50000000000000 : ℝ)*(sp4) + (7295366581/50000000000000 : ℝ)*(sp7) + (1025669434919709/50000000000000 : ℝ)*(f.failure) + (2391495781614911/50000000000000 : ℝ)*(f.sum) + (142555437198451/22530000000000000000000000000 : ℝ)*base66 + (1972522737018745841/1126500000000000000000000000000000 : ℝ)*base67 + (5649779050296745841/1126500000000000000000000000000000 : ℝ)*base69 + (1943174727087754159/1126500000000000000000000000000000 : ℝ)*base72 + (125655632649811/22530000000000000000000000000 : ℝ)*base74 + (10699411477487245841/1126500000000000000000000000000000 : ℝ)*base75 + (3075529165611754159/1126500000000000000000000000000000 : ℝ)*base78 + (1624136897988754159/1126500000000000000000000000000000 : ℝ)*base80 + (110734982845351/22530000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (14370191/2500000000000000000000 : ℝ)*base89 + (14370191/2500000000000000000000 : ℝ)*base91 + (14370191/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21849998685955926071988771/5867187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (225098047/50000000000000 : ℝ)*(base19) + (141424869/25000000000000 : ℝ)*(base23) + (3832859/5000000000000 : ℝ)*(upper3) + (39462029/100000000000000 : ℝ)*(lower4) + (1045871/1562500000000 : ℝ)*(upper5) + (3372227815469/97656250000 : ℝ)*(major0) + (3372227815469/97656250000 : ℝ)*(major1) + (3372227815469/97656250000 : ℝ)*(major2) + (7118825637/100000000000000 : ℝ)*(sp1) + (1946928553/20000000000000 : ℝ)*(sp2) + (966675015503999/20000000000000 : ℝ)*(sp4) + (966673501699653/20000000000000 : ℝ)*(sp5) + (2416682388588877/50000000000000 : ℝ)*(sp6) + (518236841105953/25000000000000 : ℝ)*(sp7) + (518236841105953/25000000000000 : ℝ)*(f.failure) + (966675015503999/20000000000000 : ℝ)*(f.sum) + (4057000339987/2816250000000000000000000000 : ℝ)*base66 + (7990155991483319/4400390625000000000000000000000 : ℝ)*base68 + (75436058413024073/35203125000000000000000000000000 : ℝ)*base69 + (18335628399733319/4400390625000000000000000000000 : ℝ)*base72 + (75069960260263/11265000000000000000000000000 : ℝ)*base74 + (138946175500419763/8800781250000000000000000000000 : ℝ)*base76 + (36543791504136401/17601562500000000000000000000000 : ℝ)*base78 + (226532246511636401/17601562500000000000000000000000 : ℝ)*base80 + (5108029412701/5632500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (812347/1250000000000000000000 : ℝ)*base89 + (812347/1250000000000000000000 : ℝ)*base91 + (812347/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1552_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83291099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1941/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5511/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11057/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1552_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1552_s5_0 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-905250683/5000000000 : ℝ)*x 0 + (1085619143/2000000000 : ℝ)*x 1 + (2609698063/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (905250683/5000000000 : ℝ)^4601 ≤ (346877734227/3125000000000 : ℝ)^3577 := by
    have hnat : (905250683 : ℕ)^4601*3125000000000^3577 ≤ 346877734227^3577*5000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905250683 5000000000 346877734227 3125000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085619143/2000000000 : ℝ)^4601 ≤ (45570535319851/100000000000000 : ℝ)^3577 := by
    have hnat : (1085619143 : ℕ)^4601*100000000000000^3577 ≤ 45570535319851^3577*2000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085619143 2000000000 45570535319851 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609698063/5000000000 : ℝ)^4601 ≤ (1083234429497/2500000000000 : ℝ)^3577 := by
    have hnat : (2609698063 : ℕ)^4601*2500000000000^3577 ≤ 1083234429497^3577*5000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609698063 5000000000 1083234429497 2500000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-905250683/5000000000 : ℝ), (1085619143/2000000000 : ℝ), (2609698063/5000000000 : ℝ)] ![(346877734227/3125000000000 : ℝ), (45570535319851/100000000000000 : ℝ), (1083234429497/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-905250683/5000000000 : ℝ)|^4601 ≤ (346877734227/3125000000000 : ℝ)^3577
        have hw : |(-905250683/5000000000 : ℝ)|=(905250683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1085619143/2000000000 : ℝ)|^4601 ≤ (45570535319851/100000000000000 : ℝ)^3577
        have hw : |(1085619143/2000000000 : ℝ)|=(1085619143/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609698063/5000000000 : ℝ)|^4601 ≤ (1083234429497/2500000000000 : ℝ)^3577
        have hw : |(2609698063/5000000000 : ℝ)|=(2609698063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s5_1 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349285267/10000000000 : ℝ)*x 0 + (-1917304609/10000000000 : ℝ)*x 1 + (1304849027/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349285267/10000000000 : ℝ)^4601 ≤ (44721262766153/100000000000000 : ℝ)^3577 := by
    have hnat : (5349285267 : ℕ)^4601*100000000000000^3577 ≤ 44721262766153^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349285267 10000000000 44721262766153 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1917304609/10000000000 : ℝ)^4601 ≤ (1194936022647/10000000000000 : ℝ)^3577 := by
    have hnat : (1917304609 : ℕ)^4601*10000000000000^3577 ≤ 1194936022647^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1917304609 10000000000 1194936022647 10000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304849027/2500000000 : ℝ)^4601 ≤ (43329376987673/100000000000000 : ℝ)^3577 := by
    have hnat : (1304849027 : ℕ)^4601*100000000000000^3577 ≤ 43329376987673^3577*2500000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304849027 2500000000 43329376987673 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349285267/10000000000 : ℝ), (-1917304609/10000000000 : ℝ), (1304849027/2500000000 : ℝ)] ![(44721262766153/100000000000000 : ℝ), (1194936022647/10000000000000 : ℝ), (43329376987673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349285267/10000000000 : ℝ)|^4601 ≤ (44721262766153/100000000000000 : ℝ)^3577
        have hw : |(5349285267/10000000000 : ℝ)|=(5349285267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1917304609/10000000000 : ℝ)|^4601 ≤ (1194936022647/10000000000000 : ℝ)^3577
        have hw : |(-1917304609/10000000000 : ℝ)|=(1917304609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304849027/2500000000 : ℝ)|^4601 ≤ (43329376987673/100000000000000 : ℝ)^3577
        have hw : |(1304849027/2500000000 : ℝ)|=(1304849027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s5_2 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668660663/1250000000 : ℝ)*x 0 + (2609698037/5000000000 : ℝ)*x 1 + (-383460921/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668660663/1250000000 : ℝ)^4601 ≤ (22360631582017/50000000000000 : ℝ)^3577 := by
    have hnat : (668660663 : ℕ)^4601*50000000000000^3577 ≤ 22360631582017^3577*1250000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668660663 1250000000 22360631582017 50000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609698037/5000000000 : ℝ)^4601 ≤ (5416172078077/12500000000000 : ℝ)^3577 := by
    have hnat : (2609698037 : ℕ)^4601*12500000000000^3577 ≤ 5416172078077^3577*5000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609698037 5000000000 5416172078077 12500000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (383460921/2000000000 : ℝ)^4601 ≤ (2987340048601/25000000000000 : ℝ)^3577 := by
    have hnat : (383460921 : ℕ)^4601*25000000000000^3577 ≤ 2987340048601^3577*2000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      383460921 2000000000 2987340048601 25000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668660663/1250000000 : ℝ), (2609698037/5000000000 : ℝ), (-383460921/2000000000 : ℝ)] ![(22360631582017/50000000000000 : ℝ), (5416172078077/12500000000000 : ℝ), (2987340048601/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668660663/1250000000 : ℝ)|^4601 ≤ (22360631582017/50000000000000 : ℝ)^3577
        have hw : |(668660663/1250000000 : ℝ)|=(668660663/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609698037/5000000000 : ℝ)|^4601 ≤ (5416172078077/12500000000000 : ℝ)^3577
        have hw : |(2609698037/5000000000 : ℝ)|=(2609698037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-383460921/2000000000 : ℝ)|^4601 ≤ (2987340048601/25000000000000 : ℝ)^3577
        have hw : |(-383460921/2000000000 : ℝ)|=(383460921/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s5_3 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (850299873/2000000000 : ℝ)*x 0 + (802782657/2000000000 : ℝ)*x 1 + (2250263277/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (850299873/2000000000 : ℝ)^4601 ≤ (16640777247533/50000000000000 : ℝ)^3577 := by
    have hnat : (850299873 : ℕ)^4601*50000000000000^3577 ≤ 16640777247533^3577*2000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850299873 2000000000 16640777247533 50000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (802782657/2000000000 : ℝ)^4601 ≤ (15454325117059/50000000000000 : ℝ)^3577 := by
    have hnat : (802782657 : ℕ)^4601*50000000000000^3577 ≤ 15454325117059^3577*2000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      802782657 2000000000 15454325117059 50000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2250263277/5000000000 : ℝ)^4601 ≤ (7161959051363/20000000000000 : ℝ)^3577 := by
    have hnat : (2250263277 : ℕ)^4601*20000000000000^3577 ≤ 7161959051363^3577*5000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250263277 5000000000 7161959051363 20000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(850299873/2000000000 : ℝ), (802782657/2000000000 : ℝ), (2250263277/5000000000 : ℝ)] ![(16640777247533/50000000000000 : ℝ), (15454325117059/50000000000000 : ℝ), (7161959051363/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(850299873/2000000000 : ℝ)|^4601 ≤ (16640777247533/50000000000000 : ℝ)^3577
        have hw : |(850299873/2000000000 : ℝ)|=(850299873/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(802782657/2000000000 : ℝ)|^4601 ≤ (15454325117059/50000000000000 : ℝ)^3577
        have hw : |(802782657/2000000000 : ℝ)|=(802782657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2250263277/5000000000 : ℝ)|^4601 ≤ (7161959051363/20000000000000 : ℝ)^3577
        have hw : |(2250263277/5000000000 : ℝ)|=(2250263277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s5_4 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-90526443/500000000 : ℝ)*x 0 + (5220479239/10000000000 : ℝ)*x 1 + (1356751137/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (90526443/500000000 : ℝ)^4601 ≤ (11100304315449/100000000000000 : ℝ)^3577 := by
    have hnat : (90526443 : ℕ)^4601*100000000000000^3577 ≤ 11100304315449^3577*500000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90526443 500000000 11100304315449 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220479239/10000000000 : ℝ)^4601 ≤ (677202236753/1562500000000 : ℝ)^3577 := by
    have hnat : (5220479239 : ℕ)^4601*1562500000000^3577 ≤ 677202236753^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220479239 10000000000 677202236753 1562500000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356751137/2500000000 : ℝ)^4601 ≤ (45558752515877/100000000000000 : ℝ)^3577 := by
    have hnat : (1356751137 : ℕ)^4601*100000000000000^3577 ≤ 45558752515877^3577*2500000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356751137 2500000000 45558752515877 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-90526443/500000000 : ℝ), (5220479239/10000000000 : ℝ), (1356751137/2500000000 : ℝ)] ![(11100304315449/100000000000000 : ℝ), (677202236753/1562500000000 : ℝ), (45558752515877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-90526443/500000000 : ℝ)|^4601 ≤ (11100304315449/100000000000000 : ℝ)^3577
        have hw : |(-90526443/500000000 : ℝ)|=(90526443/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220479239/10000000000 : ℝ)|^4601 ≤ (677202236753/1562500000000 : ℝ)^3577
        have hw : |(5220479239/10000000000 : ℝ)|=(5220479239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356751137/2500000000 : ℝ)|^4601 ≤ (45558752515877/100000000000000 : ℝ)^3577
        have hw : |(1356751137/2500000000 : ℝ)|=(1356751137/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s5_5 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294192637/10000000000 : ℝ)*x 0 + (-854847989/5000000000 : ℝ)*x 1 + (2713502271/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294192637/10000000000 : ℝ)^4601 ≤ (44129697288643/100000000000000 : ℝ)^3577 := by
    have hnat : (5294192637 : ℕ)^4601*100000000000000^3577 ≤ 44129697288643^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294192637 10000000000 44129697288643 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (854847989/5000000000 : ℝ)^4601 ≤ (10311550244281/100000000000000 : ℝ)^3577 := by
    have hnat : (854847989 : ℕ)^4601*100000000000000^3577 ≤ 10311550244281^3577*5000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854847989 5000000000 10311550244281 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2713502271/5000000000 : ℝ)^4601 ≤ (45558752451089/100000000000000 : ℝ)^3577 := by
    have hnat : (2713502271 : ℕ)^4601*100000000000000^3577 ≤ 45558752451089^3577*5000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713502271 5000000000 45558752451089 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294192637/10000000000 : ℝ), (-854847989/5000000000 : ℝ), (2713502271/5000000000 : ℝ)] ![(44129697288643/100000000000000 : ℝ), (10311550244281/100000000000000 : ℝ), (45558752451089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294192637/10000000000 : ℝ)|^4601 ≤ (44129697288643/100000000000000 : ℝ)^3577
        have hw : |(5294192637/10000000000 : ℝ)|=(5294192637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-854847989/5000000000 : ℝ)|^4601 ≤ (10311550244281/100000000000000 : ℝ)^3577
        have hw : |(-854847989/5000000000 : ℝ)|=(854847989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2713502271/5000000000 : ℝ)|^4601 ≤ (45558752451089/100000000000000 : ℝ)^3577
        have hw : |(2713502271/5000000000 : ℝ)|=(2713502271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s5_6 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294192663/10000000000 : ℝ)*x 0 + (2713502181/5000000000 : ℝ)*x 1 + (-26714003/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294192663/10000000000 : ℝ)^4601 ≤ (44129697567407/100000000000000 : ℝ)^3577 := by
    have hnat : (5294192663 : ℕ)^4601*100000000000000^3577 ≤ 44129697567407^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294192663 10000000000 44129697567407 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713502181/5000000000 : ℝ)^4601 ≤ (22779375253721/50000000000000 : ℝ)^3577 := by
    have hnat : (2713502181 : ℕ)^4601*50000000000000^3577 ≤ 22779375253721^3577*5000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713502181 5000000000 22779375253721 50000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26714003/156250000 : ℝ)^4601 ≤ (10311551904449/100000000000000 : ℝ)^3577 := by
    have hnat : (26714003 : ℕ)^4601*100000000000000^3577 ≤ 10311551904449^3577*156250000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26714003 156250000 10311551904449 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294192663/10000000000 : ℝ), (2713502181/5000000000 : ℝ), (-26714003/156250000 : ℝ)] ![(44129697567407/100000000000000 : ℝ), (22779375253721/50000000000000 : ℝ), (10311551904449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294192663/10000000000 : ℝ)|^4601 ≤ (44129697567407/100000000000000 : ℝ)^3577
        have hw : |(5294192663/10000000000 : ℝ)|=(5294192663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713502181/5000000000 : ℝ)|^4601 ≤ (22779375253721/50000000000000 : ℝ)^3577
        have hw : |(2713502181/5000000000 : ℝ)|=(2713502181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-26714003/156250000 : ℝ)|^4601 ≤ (10311551904449/100000000000000 : ℝ)^3577
        have hw : |(-26714003/156250000 : ℝ)|=(26714003/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1552_s5_7 (p : ℝ) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2125781617/5000000000 : ℝ)*x 0 + (4498000969/10000000000 : ℝ)*x 1 + (2008228801/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2125781617/5000000000 : ℝ)^4601 ≤ (33282197605903/100000000000000 : ℝ)^3577 := by
    have hnat : (2125781617 : ℕ)^4601*100000000000000^3577 ≤ 33282197605903^3577*5000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125781617 5000000000 33282197605903 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4498000969/10000000000 : ℝ)^4601 ≤ (35783948925837/100000000000000 : ℝ)^3577 := by
    have hnat : (4498000969 : ℕ)^4601*100000000000000^3577 ≤ 35783948925837^3577*10000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498000969 10000000000 35783948925837 100000000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2008228801/5000000000 : ℝ)^4601 ≤ (966682920319/3125000000000 : ℝ)^3577 := by
    have hnat : (2008228801 : ℕ)^4601*3125000000000^3577 ≤ 966682920319^3577*5000000000^4601 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008228801 5000000000 966682920319 3125000000000 4601 3577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4601/1024 : ℝ)) 4601 3577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2125781617/5000000000 : ℝ), (4498000969/10000000000 : ℝ), (2008228801/5000000000 : ℝ)] ![(33282197605903/100000000000000 : ℝ), (35783948925837/100000000000000 : ℝ), (966682920319/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2125781617/5000000000 : ℝ)|^4601 ≤ (33282197605903/100000000000000 : ℝ)^3577
        have hw : |(2125781617/5000000000 : ℝ)|=(2125781617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4498000969/10000000000 : ℝ)|^4601 ≤ (35783948925837/100000000000000 : ℝ)^3577
        have hw : |(4498000969/10000000000 : ℝ)|=(4498000969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2008228801/5000000000 : ℝ)|^4601 ≤ (966682920319/3125000000000 : ℝ)^3577
        have hw : |(2008228801/5000000000 : ℝ)|=(2008228801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1552_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83291099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11057/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11061/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11057/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11057/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11057/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11057/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11057/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11057/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11057/100000 : ℝ) ^ (4599/1024 : ℝ) ≤ (2533631378014917/50000000000000000000 : ℝ) := by
    have hpowers : (11057/100000 : ℝ)^4599 ≤ (2533631378014917/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11057 : ℕ)^4599*50000000000000000000^1024 ≤ 2533631378014917^1024*100000^4599 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11057 100000 2533631378014917 50000000000000000000 4599 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11057/100000 : ℝ)) (X := (2533631378014917/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4599 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15489/100000 : ℝ) ^ (4599/1024 : ℝ) ≤ (23026299230482369/100000000000000000000 : ℝ) := by
    have hpowers : (15489/100000 : ℝ)^4599 ≤ (23026299230482369/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15489 : ℕ)^4599*100000000000000000000^1024 ≤ 23026299230482369^1024*100000^4599 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15489 100000 23026299230482369 100000000000000000000 4599 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15489/100000 : ℝ)) (X := (23026299230482369/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4599 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002533631378014917/25000000000000000000 : ℝ) ≤ (2500056410879371/2500000000000000 : ℝ) ^ (4599/1024 : ℝ) := by
    have hpowers : (25002533631378014917/25000000000000000000 : ℝ)^1024 ≤ (2500056410879371/2500000000000000 : ℝ)^4599 := by
      have hnat : (25002533631378014917 : ℕ)^1024*2500000000000000^4599 ≤ 2500056410879371^4599*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002533631378014917 25000000000000000000 2500056410879371 2500000000000000 1024 4599 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500056410879371/2500000000000000 : ℝ)) (X := (25002533631378014917/25000000000000000000 : ℝ)) (by norm_num) 4599 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100028093561986512203/100000000000000000000 : ℝ) ≤ (10000625454811751/10000000000000000 : ℝ) ^ (4599/1024 : ℝ) := by
    have hpowers : (100028093561986512203/100000000000000000000 : ℝ)^1024 ≤ (10000625454811751/10000000000000000 : ℝ)^4599 := by
      have hnat : (100028093561986512203 : ℕ)^1024*10000000000000000^4599 ≤ 10000625454811751^4599*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100028093561986512203 100000000000000000000 10000625454811751 10000000000000000 1024 4599 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000625454811751/10000000000000000 : ℝ)) (X := (100028093561986512203/100000000000000000000 : ℝ)) (by norm_num) 4599 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50023026299230482369/50000000000000000000 : ℝ) ≤ (5000512633053009/5000000000000000 : ℝ) ^ (4599/1024 : ℝ) := by
    have hpowers : (50023026299230482369/50000000000000000000 : ℝ)^1024 ≤ (5000512633053009/5000000000000000 : ℝ)^4599 := by
      have hnat : (50023026299230482369 : ℕ)^1024*5000000000000000^4599 ≤ 5000512633053009^4599*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023026299230482369 50000000000000000000 5000512633053009 5000000000000000 1024 4599 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000512633053009/5000000000000000 : ℝ)) (X := (50023026299230482369/50000000000000000000 : ℝ)) (by norm_num) 4599 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2533631378014917/50000000000000000000 : ℝ) ≤ ((886243172502161373/886400000000000000 : ℝ)+2*(399811294267/443200000000000 : ℝ)*(11057/100000 : ℝ))^(4599/1024 : ℝ) := by
    rw [show (886243172502161373/886400000000000000 : ℝ)+2*(399811294267/443200000000000 : ℝ)*(11057/100000 : ℝ)=(2500056410879371/2500000000000000 : ℝ) by norm_num, show 1+2*(2533631378014917/50000000000000000000 : ℝ)=(25002533631378014917/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(23026299230482369/100000000000000000000 : ℝ)+(2533631378014917/50000000000000000000 : ℝ) ≤ ((886243172502161373/886400000000000000 : ℝ)+(399811294267/443200000000000 : ℝ)*((15489/100000 : ℝ)+(11057/100000 : ℝ)))^(4599/1024 : ℝ) := by
    rw [show (886243172502161373/886400000000000000 : ℝ)+(399811294267/443200000000000 : ℝ)*((15489/100000 : ℝ)+(11057/100000 : ℝ))=(10000625454811751/10000000000000000 : ℝ) by norm_num, show 1+(23026299230482369/100000000000000000000 : ℝ)+(2533631378014917/50000000000000000000 : ℝ)=(100028093561986512203/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(23026299230482369/100000000000000000000 : ℝ) ≤ ((886243172502161373/886400000000000000 : ℝ)+2*(399811294267/443200000000000 : ℝ)*(15489/100000 : ℝ))^(4599/1024 : ℝ) := by
    rw [show (886243172502161373/886400000000000000 : ℝ)+2*(399811294267/443200000000000 : ℝ)*(15489/100000 : ℝ)=(5000512633053009/5000000000000000 : ℝ) by norm_num, show 1+2*(23026299230482369/100000000000000000000 : ℝ)=(50023026299230482369/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (886243172502161373/886400000000000000 : ℝ)*(X 1 0+X 2 0)+(399811294267/443200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4599/1024 : ℝ)) (lo := (11057/100000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (886243172502161373/886400000000000000 : ℝ)) (alpha := (399811294267/443200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (886243172502161373/886400000000000000 : ℝ)*(X 0 1+X 2 1)+(399811294267/443200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4599/1024 : ℝ)) (lo := (11057/100000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (886243172502161373/886400000000000000 : ℝ)) (alpha := (399811294267/443200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (886243172502161373/886400000000000000 : ℝ)*(X 0 2+X 1 2)+(399811294267/443200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4599/1024 : ℝ)) (lo := (11057/100000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (886243172502161373/886400000000000000 : ℝ)) (alpha := (399811294267/443200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-905250683/5000000000 : ℝ)*X 0 0+(1085619143/2000000000 : ℝ)*X 0 1+(2609698063/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349285267/10000000000 : ℝ)*X 1 0+(-1917304609/10000000000 : ℝ)*X 1 1+(1304849027/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668660663/1250000000 : ℝ)*X 2 0+(2609698037/5000000000 : ℝ)*X 2 1+(-383460921/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((850299873/2000000000 : ℝ)*X 0 0+(802782657/2000000000 : ℝ)*X 0 1+(2250263277/5000000000 : ℝ)*X 0 2+(850299873/2000000000 : ℝ)*X 1 0+(802782657/2000000000 : ℝ)*X 1 1+(2250263277/5000000000 : ℝ)*X 1 2+(850299873/2000000000 : ℝ)*X 2 0+(802782657/2000000000 : ℝ)*X 2 1+(2250263277/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-90526443/500000000 : ℝ)*X 0 0+(5220479239/10000000000 : ℝ)*X 0 1+(1356751137/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294192637/10000000000 : ℝ)*X 1 0+(-854847989/5000000000 : ℝ)*X 1 1+(2713502271/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294192663/10000000000 : ℝ)*X 2 0+(2713502181/5000000000 : ℝ)*X 2 1+(-26714003/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2125781617/5000000000 : ℝ)*X 0 0+(4498000969/10000000000 : ℝ)*X 0 1+(2008228801/5000000000 : ℝ)*X 0 2+(2125781617/5000000000 : ℝ)*X 1 0+(4498000969/10000000000 : ℝ)*X 1 1+(2008228801/5000000000 : ℝ)*X 1 2+(2125781617/5000000000 : ℝ)*X 2 0+(4498000969/10000000000 : ℝ)*X 2 1+(2008228801/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1552_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9104659719075834831333/1108000000000000000000000000 : ℝ) := by norm_num
    linear_combination (70032961/5000000000000 : ℝ)*(base19) + (1346056033/100000000000000 : ℝ)*(base23) + (23468899/50000000000000 : ℝ)*(lower2) + (4818749/2500000000000 : ℝ)*(upper3) + (17325741/12500000000000 : ℝ)*(upper5) + (171166553786431/5000000000000 : ℝ)*(major0) + (171166553786431/5000000000000 : ℝ)*(major1) + (171166553786431/5000000000000 : ℝ)*(major2) + (239579957991537/5000000000000 : ℝ)*(sp0) + (4791620312438281/100000000000000 : ℝ)*(sp1) + (4791620367041469/100000000000000 : ℝ)*(sp2) + (2055029558455733/100000000000000 : ℝ)*(sp3) + (22553266761/100000000000000 : ℝ)*(sp4) + (5302998633/50000000000000 : ℝ)*(sp7) + (1027520082226499/50000000000000 : ℝ)*(f.failure) + (4791621713097501/100000000000000 : ℝ)*(f.sum) + (362912192547/221600000000000000000000000 : ℝ)*base66 + (24925467449732237/4432000000000000000000000000000 : ℝ)*base68 + (15369944841659763/4432000000000000000000000000000 : ℝ)*base69 + (16492830449371763/4432000000000000000000000000000 : ℝ)*base71 + (6435931504163/1108000000000000000000000000 : ℝ)*base74 + (4421896088900237/4432000000000000000000000000000 : ℝ)*base76 + (4614336736203763/4432000000000000000000000000000 : ℝ)*base77 + (2522765487796237/4432000000000000000000000000000 : ℝ)*base80 + (9872784343/44320000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (31367599/2500000000000000000000 : ℝ)*base90 + (31367599/2500000000000000000000 : ℝ)*base92 + (31367599/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (199106084759954549951517927/44320000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1071372941/100000000000000 : ℝ)*(base19) + (1091690633/100000000000000 : ℝ)*(base23) + (299304077/100000000000000 : ℝ)*(lower1) + (24836357/100000000000000 : ℝ)*(upper2) + (87230913/100000000000000 : ℝ)*(upper3) + (109878227/100000000000000 : ℝ)*(upper5) + (3459328353169967/100000000000000 : ℝ)*(major0) + (3459328353169967/100000000000000 : ℝ)*(major1) + (3459328353169967/100000000000000 : ℝ)*(major2) + (2420377777/50000000000000 : ℝ)*(sp1) + (4842007073811413/100000000000000 : ℝ)*(sp4) + (4842001161682919/100000000000000 : ℝ)*(sp5) + (242100299106039/5000000000000 : ℝ)*(sp6) + (1038324741389823/50000000000000 : ℝ)*(sp7) + (1038324741389823/50000000000000 : ℝ)*(f.failure) + (4842007073811413/100000000000000 : ℝ)*(f.sum) + (83967151073749/22160000000000000000000000000 : ℝ)*base65 + (1124390414685622691/88640000000000000000000000000000 : ℝ)*base67 + (2184216676256777309/88640000000000000000000000000000 : ℝ)*base70 + (657355667899062691/88640000000000000000000000000000 : ℝ)*base71 + (43058177338229/22160000000000000000000000000 : ℝ)*base73 + (62041726772617309/88640000000000000000000000000000 : ℝ)*base76 + (1526316029862902691/88640000000000000000000000000000 : ℝ)*base77 + (689780725123702691/88640000000000000000000000000000 : ℝ)*base79 + (4545277085931/22160000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (29914523/2500000000000000000000 : ℝ)*base90 + (29914523/2500000000000000000000 : ℝ)*base92 + (29914523/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1552_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83291099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11057/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11061/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1552_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1552_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83291099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7931/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5357/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11061/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1552_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1552_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1552_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4599/1024 : ℝ) ≤ p) (hpb : p ≤ (4601/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83291099/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7931/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5357/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11061/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1552_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

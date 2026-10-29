-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1707_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:49:59.828269+00:00
-- url     : https://prove2.me/submissions/89cb8a23-4908-4f4e-aced-b9db2e4f78c0

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
theorem support_rectangle_w1707_s0_0 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1345469911/10000000000 : ℝ)*x 0 + (570389107/1000000000 : ℝ)*x 1 + (4957006247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345469911/10000000000 : ℝ)^5279 ≤ (8302913313327/100000000000000 : ℝ)^4255 := by
    have hnat : (1345469911 : ℕ)^5279*100000000000000^4255 ≤ 8302913313327^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345469911 10000000000 8302913313327 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (570389107/1000000000 : ℝ)^5279 ≤ (6228764026223/12500000000000 : ℝ)^4255 := by
    have hnat : (570389107 : ℕ)^5279*12500000000000^4255 ≤ 6228764026223^4255*1000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      570389107 1000000000 6228764026223 12500000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4957006247/10000000000 : ℝ)^5279 ≤ (5233371807303/12500000000000 : ℝ)^4255 := by
    have hnat : (4957006247 : ℕ)^5279*12500000000000^4255 ≤ 5233371807303^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4957006247 10000000000 5233371807303 12500000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1345469911/10000000000 : ℝ), (570389107/1000000000 : ℝ), (4957006247/10000000000 : ℝ)] ![(8302913313327/100000000000000 : ℝ), (6228764026223/12500000000000 : ℝ), (5233371807303/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1345469911/10000000000 : ℝ)|^5279 ≤ (8302913313327/100000000000000 : ℝ)^4255
        have hw : |(-1345469911/10000000000 : ℝ)|=(1345469911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(570389107/1000000000 : ℝ)|^5279 ≤ (6228764026223/12500000000000 : ℝ)^4255
        have hw : |(570389107/1000000000 : ℝ)|=(570389107/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4957006247/10000000000 : ℝ)|^5279 ≤ (5233371807303/12500000000000 : ℝ)^4255
        have hw : |(4957006247/10000000000 : ℝ)|=(4957006247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_s0_1 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1081275891/2000000000 : ℝ)*x 0 + (-437575959/2500000000 : ℝ)*x 1 + (991401141/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081275891/2000000000 : ℝ)^5279 ≤ (2331300911457/5000000000000 : ℝ)^4255 := by
    have hnat : (1081275891 : ℕ)^5279*5000000000000^4255 ≤ 2331300911457^4255*2000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081275891 2000000000 2331300911457 5000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (437575959/2500000000 : ℝ)^5279 ≤ (11507012969683/100000000000000 : ℝ)^4255 := by
    have hnat : (437575959 : ℕ)^5279*100000000000000^4255 ≤ 11507012969683^4255*2500000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437575959 2500000000 11507012969683 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (991401141/2000000000 : ℝ)^5279 ≤ (41866968779011/100000000000000 : ℝ)^4255 := by
    have hnat : (991401141 : ℕ)^5279*100000000000000^4255 ≤ 41866968779011^4255*2000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      991401141 2000000000 41866968779011 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081275891/2000000000 : ℝ), (-437575959/2500000000 : ℝ), (991401141/2000000000 : ℝ)] ![(2331300911457/5000000000000 : ℝ), (11507012969683/100000000000000 : ℝ), (41866968779011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081275891/2000000000 : ℝ)|^5279 ≤ (2331300911457/5000000000000 : ℝ)^4255
        have hw : |(1081275891/2000000000 : ℝ)|=(1081275891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-437575959/2500000000 : ℝ)|^5279 ≤ (11507012969683/100000000000000 : ℝ)^4255
        have hw : |(-437575959/2500000000 : ℝ)|=(437575959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(991401141/2000000000 : ℝ)|^5279 ≤ (41866968779011/100000000000000 : ℝ)^4255
        have hw : |(991401141/2000000000 : ℝ)|=(991401141/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_s0_2 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5406378347/10000000000 : ℝ)*x 0 + (1239251597/2500000000 : ℝ)*x 1 + (-437576103/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5406378347/10000000000 : ℝ)^5279 ≤ (4662600637381/10000000000000 : ℝ)^4255 := by
    have hnat : (5406378347 : ℕ)^5279*10000000000000^4255 ≤ 4662600637381^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406378347 10000000000 4662600637381 10000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1239251597/2500000000 : ℝ)^5279 ≤ (4186697593591/10000000000000 : ℝ)^4255 := by
    have hnat : (1239251597 : ℕ)^5279*10000000000000^4255 ≤ 4186697593591^4255*2500000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1239251597 2500000000 4186697593591 10000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (437576103/2500000000 : ℝ)^5279 ≤ (11507017667799/100000000000000 : ℝ)^4255 := by
    have hnat : (437576103 : ℕ)^5279*100000000000000^4255 ≤ 11507017667799^4255*2500000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437576103 2500000000 11507017667799 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5406378347/10000000000 : ℝ), (1239251597/2500000000 : ℝ), (-437576103/2500000000 : ℝ)] ![(4662600637381/10000000000000 : ℝ), (4186697593591/10000000000000 : ℝ), (11507017667799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5406378347/10000000000 : ℝ)|^5279 ≤ (4662600637381/10000000000000 : ℝ)^4255
        have hw : |(5406378347/10000000000 : ℝ)|=(5406378347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1239251597/2500000000 : ℝ)|^5279 ≤ (4186697593591/10000000000000 : ℝ)^4255
        have hw : |(1239251597/2500000000 : ℝ)|=(1239251597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-437576103/2500000000 : ℝ)|^5279 ≤ (11507017667799/100000000000000 : ℝ)^4255
        have hw : |(-437576103/2500000000 : ℝ)|=(437576103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_s0_3 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4042092131/10000000000 : ℝ)*x 0 + (3057190827/10000000000 : ℝ)*x 1 + (5207768377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4042092131/10000000000 : ℝ)^5279 ≤ (1625185092133/5000000000000 : ℝ)^4255 := by
    have hnat : (4042092131 : ℕ)^5279*5000000000000^4255 ≤ 1625185092133^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4042092131 10000000000 1625185092133 5000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3057190827/10000000000 : ℝ)^5279 ≤ (22985887465151/100000000000000 : ℝ)^4255 := by
    have hnat : (3057190827 : ℕ)^5279*100000000000000^4255 ≤ 22985887465151^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3057190827 10000000000 22985887465151 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5207768377/10000000000 : ℝ)^5279 ≤ (22255205339401/50000000000000 : ℝ)^4255 := by
    have hnat : (5207768377 : ℕ)^5279*50000000000000^4255 ≤ 22255205339401^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5207768377 10000000000 22255205339401 50000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4042092131/10000000000 : ℝ), (3057190827/10000000000 : ℝ), (5207768377/10000000000 : ℝ)] ![(1625185092133/5000000000000 : ℝ), (22985887465151/100000000000000 : ℝ), (22255205339401/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4042092131/10000000000 : ℝ)|^5279 ≤ (1625185092133/5000000000000 : ℝ)^4255
        have hw : |(4042092131/10000000000 : ℝ)|=(4042092131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3057190827/10000000000 : ℝ)|^5279 ≤ (22985887465151/100000000000000 : ℝ)^4255
        have hw : |(3057190827/10000000000 : ℝ)|=(3057190827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5207768377/10000000000 : ℝ)|^5279 ≤ (22255205339401/50000000000000 : ℝ)^4255
        have hw : |(5207768377/10000000000 : ℝ)|=(5207768377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_s0_4 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-269437423/2000000000 : ℝ)*x 0 + (4975420341/10000000000 : ℝ)*x 1 + (5684859761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269437423/2000000000 : ℝ)^5279 ≤ (2079015611993/25000000000000 : ℝ)^4255 := by
    have hnat : (269437423 : ℕ)^5279*25000000000000^4255 ≤ 2079015611993^4255*2000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269437423 2000000000 2079015611993 25000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4975420341/10000000000 : ℝ)^5279 ≤ (42060014972729/100000000000000 : ℝ)^4255 := by
    have hnat : (4975420341 : ℕ)^5279*100000000000000^4255 ≤ 42060014972729^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4975420341 10000000000 42060014972729 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5684859761/10000000000 : ℝ)^5279 ≤ (1984956902499/4000000000000 : ℝ)^4255 := by
    have hnat : (5684859761 : ℕ)^5279*4000000000000^4255 ≤ 1984956902499^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5684859761 10000000000 1984956902499 4000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-269437423/2000000000 : ℝ), (4975420341/10000000000 : ℝ), (5684859761/10000000000 : ℝ)] ![(2079015611993/25000000000000 : ℝ), (42060014972729/100000000000000 : ℝ), (1984956902499/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-269437423/2000000000 : ℝ)|^5279 ≤ (2079015611993/25000000000000 : ℝ)^4255
        have hw : |(-269437423/2000000000 : ℝ)|=(269437423/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4975420341/10000000000 : ℝ)|^5279 ≤ (42060014972729/100000000000000 : ℝ)^4255
        have hw : |(4975420341/10000000000 : ℝ)|=(4975420341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5684859761/10000000000 : ℝ)|^5279 ≤ (1984956902499/4000000000000 : ℝ)^4255
        have hw : |(5684859761/10000000000 : ℝ)|=(5684859761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_s0_5 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5203950143/10000000000 : ℝ)*x 0 + (-1022450093/10000000000 : ℝ)*x 1 + (355303737/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5203950143/10000000000 : ℝ)^5279 ≤ (44469926414093/100000000000000 : ℝ)^4255 := by
    have hnat : (5203950143 : ℕ)^5279*100000000000000^4255 ≤ 44469926414093^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5203950143 10000000000 44469926414093 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1022450093/10000000000 : ℝ)^5279 ≤ (1181230136681/20000000000000 : ℝ)^4255 := by
    have hnat : (1022450093 : ℕ)^5279*20000000000000^4255 ≤ 1181230136681^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022450093 10000000000 1181230136681 20000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (355303737/625000000 : ℝ)^5279 ≤ (49623922898201/100000000000000 : ℝ)^4255 := by
    have hnat : (355303737 : ℕ)^5279*100000000000000^4255 ≤ 49623922898201^4255*625000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355303737 625000000 49623922898201 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5203950143/10000000000 : ℝ), (-1022450093/10000000000 : ℝ), (355303737/625000000 : ℝ)] ![(44469926414093/100000000000000 : ℝ), (1181230136681/20000000000000 : ℝ), (49623922898201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5203950143/10000000000 : ℝ)|^5279 ≤ (44469926414093/100000000000000 : ℝ)^4255
        have hw : |(5203950143/10000000000 : ℝ)|=(5203950143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1022450093/10000000000 : ℝ)|^5279 ≤ (1181230136681/20000000000000 : ℝ)^4255
        have hw : |(-1022450093/10000000000 : ℝ)|=(1022450093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(355303737/625000000 : ℝ)|^5279 ≤ (49623922898201/100000000000000 : ℝ)^4255
        have hw : |(355303737/625000000 : ℝ)|=(355303737/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_s0_6 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1040789979/2000000000 : ℝ)*x 0 + (5684860447/10000000000 : ℝ)*x 1 + (-1022449469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1040789979/2000000000 : ℝ)^5279 ≤ (11117480946203/25000000000000 : ℝ)^4255 := by
    have hnat : (1040789979 : ℕ)^5279*25000000000000^4255 ≤ 11117480946203^4255*2000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040789979 2000000000 11117480946203 25000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5684860447/10000000000 : ℝ)^5279 ≤ (49623929991769/100000000000000 : ℝ)^4255 := by
    have hnat : (5684860447 : ℕ)^5279*100000000000000^4255 ≤ 49623929991769^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5684860447 10000000000 49623929991769 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1022449469/10000000000 : ℝ)^5279 ≤ (5906146211433/100000000000000 : ℝ)^4255 := by
    have hnat : (1022449469 : ℕ)^5279*100000000000000^4255 ≤ 5906146211433^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022449469 10000000000 5906146211433 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1040789979/2000000000 : ℝ), (5684860447/10000000000 : ℝ), (-1022449469/10000000000 : ℝ)] ![(11117480946203/25000000000000 : ℝ), (49623929991769/100000000000000 : ℝ), (5906146211433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1040789979/2000000000 : ℝ)|^5279 ≤ (11117480946203/25000000000000 : ℝ)^4255
        have hw : |(1040789979/2000000000 : ℝ)|=(1040789979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5684860447/10000000000 : ℝ)|^5279 ≤ (49623929991769/100000000000000 : ℝ)^4255
        have hw : |(5684860447/10000000000 : ℝ)|=(5684860447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1022449469/10000000000 : ℝ)|^5279 ≤ (5906146211433/100000000000000 : ℝ)^4255
        have hw : |(-1022449469/10000000000 : ℝ)|=(1022449469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_s0_7 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2023516231/5000000000 : ℝ)*x 0 + (5154747397/10000000000 : ℝ)*x 1 + (3111987067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2023516231/5000000000 : ℝ)^5279 ≤ (32552996358919/100000000000000 : ℝ)^4255 := by
    have hnat : (2023516231 : ℕ)^5279*100000000000000^4255 ≤ 32552996358919^4255*5000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2023516231 5000000000 32552996358919 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5154747397/10000000000 : ℝ)^5279 ≤ (43948876705793/100000000000000 : ℝ)^4255 := by
    have hnat : (5154747397 : ℕ)^5279*100000000000000^4255 ≤ 43948876705793^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5154747397 10000000000 43948876705793 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3111987067/10000000000 : ℝ)^5279 ≤ (23498126925517/100000000000000 : ℝ)^4255 := by
    have hnat : (3111987067 : ℕ)^5279*100000000000000^4255 ≤ 23498126925517^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3111987067 10000000000 23498126925517 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2023516231/5000000000 : ℝ), (5154747397/10000000000 : ℝ), (3111987067/10000000000 : ℝ)] ![(32552996358919/100000000000000 : ℝ), (43948876705793/100000000000000 : ℝ), (23498126925517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2023516231/5000000000 : ℝ)|^5279 ≤ (32552996358919/100000000000000 : ℝ)^4255
        have hw : |(2023516231/5000000000 : ℝ)|=(2023516231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5154747397/10000000000 : ℝ)|^5279 ≤ (43948876705793/100000000000000 : ℝ)^4255
        have hw : |(5154747397/10000000000 : ℝ)|=(5154747397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3111987067/10000000000 : ℝ)|^5279 ≤ (23498126925517/100000000000000 : ℝ)^4255
        have hw : |(3111987067/10000000000 : ℝ)|=(3111987067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_s0_8 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (17513403/10000000000 : ℝ)*x 0 + (2551876093/5000000000 : ℝ)*x 1 + (1579088253/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17513403/10000000000 : ℝ)^5279 ≤ (7603183439/20000000000000 : ℝ)^4255 := by
    have hnat : (17513403 : ℕ)^5279*20000000000000^4255 ≤ 7603183439^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17513403 10000000000 7603183439 20000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2551876093/5000000000 : ℝ)^5279 ≤ (21705053425083/50000000000000 : ℝ)^4255 := by
    have hnat : (2551876093 : ℕ)^5279*50000000000000^4255 ≤ 21705053425083^4255*5000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2551876093 5000000000 21705053425083 50000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1579088253/2500000000 : ℝ)^5279 ≤ (56551877218453/100000000000000 : ℝ)^4255 := by
    have hnat : (1579088253 : ℕ)^5279*100000000000000^4255 ≤ 56551877218453^4255*2500000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1579088253 2500000000 56551877218453 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(17513403/10000000000 : ℝ), (2551876093/5000000000 : ℝ), (1579088253/2500000000 : ℝ)] ![(7603183439/20000000000000 : ℝ), (21705053425083/50000000000000 : ℝ), (56551877218453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(17513403/10000000000 : ℝ)|^5279 ≤ (7603183439/20000000000000 : ℝ)^4255
        have hw : |(17513403/10000000000 : ℝ)|=(17513403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2551876093/5000000000 : ℝ)|^5279 ≤ (21705053425083/50000000000000 : ℝ)^4255
        have hw : |(2551876093/5000000000 : ℝ)|=(2551876093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1579088253/2500000000 : ℝ)|^5279 ≤ (56551877218453/100000000000000 : ℝ)^4255
        have hw : |(1579088253/2500000000 : ℝ)|=(1579088253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_s0_9 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (690306259/5000000000 : ℝ)*x 0 + (-3111426057/10000000000 : ℝ)*x 1 + (183062723/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (690306259/5000000000 : ℝ)^5279 ≤ (8572809343339/100000000000000 : ℝ)^4255 := by
    have hnat : (690306259 : ℕ)^5279*100000000000000^4255 ≤ 8572809343339^4255*5000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      690306259 5000000000 8572809343339 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3111426057/10000000000 : ℝ)^5279 ≤ (469857429793/2000000000000 : ℝ)^4255 := by
    have hnat : (3111426057 : ℕ)^5279*2000000000000^4255 ≤ 469857429793^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3111426057 10000000000 469857429793 2000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (183062723/250000000 : ℝ)^5279 ≤ (84917898939/125000000000 : ℝ)^4255 := by
    have hnat : (183062723 : ℕ)^5279*125000000000^4255 ≤ 84917898939^4255*250000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183062723 250000000 84917898939 125000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(690306259/5000000000 : ℝ), (-3111426057/10000000000 : ℝ), (183062723/250000000 : ℝ)] ![(8572809343339/100000000000000 : ℝ), (469857429793/2000000000000 : ℝ), (84917898939/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(690306259/5000000000 : ℝ)|^5279 ≤ (8572809343339/100000000000000 : ℝ)^4255
        have hw : |(690306259/5000000000 : ℝ)|=(690306259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3111426057/10000000000 : ℝ)|^5279 ≤ (469857429793/2000000000000 : ℝ)^4255
        have hw : |(-3111426057/10000000000 : ℝ)|=(3111426057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(183062723/250000000 : ℝ)|^5279 ≤ (84917898939/125000000000 : ℝ)^4255
        have hw : |(183062723/250000000 : ℝ)|=(183062723/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_s0_10 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (690307271/5000000000 : ℝ)*x 0 + (3661256957/5000000000 : ℝ)*x 1 + (-3111418257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (690307271/5000000000 : ℝ)^5279 ≤ (8572824935777/100000000000000 : ℝ)^4255 := by
    have hnat : (690307271 : ℕ)^5279*100000000000000^4255 ≤ 8572824935777^4255*5000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      690307271 5000000000 8572824935777 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3661256957/5000000000 : ℝ)^5279 ≤ (67934376632951/100000000000000 : ℝ)^4255 := by
    have hnat : (3661256957 : ℕ)^5279*100000000000000^4255 ≤ 67934376632951^4255*5000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3661256957 5000000000 67934376632951 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3111418257/10000000000 : ℝ)^5279 ≤ (2936599802791/12500000000000 : ℝ)^4255 := by
    have hnat : (3111418257 : ℕ)^5279*12500000000000^4255 ≤ 2936599802791^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3111418257 10000000000 2936599802791 12500000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(690307271/5000000000 : ℝ), (3661256957/5000000000 : ℝ), (-3111418257/10000000000 : ℝ)] ![(8572824935777/100000000000000 : ℝ), (67934376632951/100000000000000 : ℝ), (2936599802791/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(690307271/5000000000 : ℝ)|^5279 ≤ (8572824935777/100000000000000 : ℝ)^4255
        have hw : |(690307271/5000000000 : ℝ)|=(690307271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3661256957/5000000000 : ℝ)|^5279 ≤ (67934376632951/100000000000000 : ℝ)^4255
        have hw : |(3661256957/5000000000 : ℝ)|=(3661256957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3111418257/10000000000 : ℝ)|^5279 ≤ (2936599802791/12500000000000 : ℝ)^4255
        have hw : |(-3111418257/10000000000 : ℝ)|=(3111418257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_s0_11 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (462790771/2000000000 : ℝ)*x 0 + (1368928843/2500000000 : ℝ)*x 1 + (2212247959/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (462790771/2000000000 : ℝ)^5279 ≤ (3253954906863/20000000000000 : ℝ)^4255 := by
    have hnat : (462790771 : ℕ)^5279*20000000000000^4255 ≤ 3253954906863^4255*2000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      462790771 2000000000 3253954906863 20000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1368928843/2500000000 : ℝ)^5279 ≤ (5921129605183/12500000000000 : ℝ)^4255 := by
    have hnat : (1368928843 : ℕ)^5279*12500000000000^4255 ≤ 5921129605183^4255*2500000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368928843 2500000000 5921129605183 12500000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2212247959/5000000000 : ℝ)^5279 ≤ (1818059430263/5000000000000 : ℝ)^4255 := by
    have hnat : (2212247959 : ℕ)^5279*5000000000000^4255 ≤ 1818059430263^4255*5000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2212247959 5000000000 1818059430263 5000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(462790771/2000000000 : ℝ), (1368928843/2500000000 : ℝ), (2212247959/5000000000 : ℝ)] ![(3253954906863/20000000000000 : ℝ), (5921129605183/12500000000000 : ℝ), (1818059430263/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(462790771/2000000000 : ℝ)|^5279 ≤ (3253954906863/20000000000000 : ℝ)^4255
        have hw : |(462790771/2000000000 : ℝ)|=(462790771/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1368928843/2500000000 : ℝ)|^5279 ≤ (5921129605183/12500000000000 : ℝ)^4255
        have hw : |(1368928843/2500000000 : ℝ)|=(1368928843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2212247959/5000000000 : ℝ)|^5279 ≤ (1818059430263/5000000000000 : ℝ)^4255
        have hw : |(2212247959/5000000000 : ℝ)|=(2212247959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1707_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24246241/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (5963/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (11007/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5271/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5271 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5271*1^1024 ≤ 0^1024*1^5271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5271 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5271 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5271/1024 : ℝ) ≤ (178916068143083077/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5271 ≤ (178916068143083077/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5271*20000000000000000000^1024 ≤ 178916068143083077^1024*5^5271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 178916068143083077 20000000000000000000 5271 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (178916068143083077/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5271 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5271/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5271 := by
      have hnat : (1 : ℕ)^1024*1^5271 ≤ 1^5271*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5271 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20178916068143083077/20000000000000000000 : ℝ) ≤ (5008658381109233/5000000000000000 : ℝ) ^ (5271/1024 : ℝ) := by
    have hpowers : (20178916068143083077/20000000000000000000 : ℝ)^1024 ≤ (5008658381109233/5000000000000000 : ℝ)^5271 := by
      have hnat : (20178916068143083077 : ℕ)^1024*5000000000000000^5271 ≤ 5008658381109233^5271*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20178916068143083077 20000000000000000000 5008658381109233 5000000000000000 1024 5271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5008658381109233/5000000000000000 : ℝ)) (X := (20178916068143083077/20000000000000000000 : ℝ)) (by norm_num) 5271 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10178916068143083077/10000000000000000000 : ℝ) ≤ (2508658381109233/2500000000000000 : ℝ) ^ (5271/1024 : ℝ) := by
    have hpowers : (10178916068143083077/10000000000000000000 : ℝ)^1024 ≤ (2508658381109233/2500000000000000 : ℝ)^5271 := by
      have hnat : (10178916068143083077 : ℕ)^1024*2500000000000000^5271 ≤ 2508658381109233^5271*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10178916068143083077 10000000000000000000 2508658381109233 2500000000000000 1024 5271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2508658381109233/2500000000000000 : ℝ)) (X := (10178916068143083077/10000000000000000000 : ℝ)) (by norm_num) 5271 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(8658381109233/2000000000000000 : ℝ)*(0 : ℝ))^(5271/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(8658381109233/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(178916068143083077/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(8658381109233/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5271/1024 : ℝ) := by
    rw [show (1 : ℝ)+(8658381109233/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5008658381109233/5000000000000000 : ℝ) by norm_num, show 1+(178916068143083077/20000000000000000000 : ℝ)+(0 : ℝ)=(20178916068143083077/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(178916068143083077/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(8658381109233/2000000000000000 : ℝ)*(2/5 : ℝ))^(5271/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(8658381109233/2000000000000000 : ℝ)*(2/5 : ℝ)=(2508658381109233/2500000000000000 : ℝ) by norm_num, show 1+2*(178916068143083077/20000000000000000000 : ℝ)=(10178916068143083077/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(8658381109233/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5271/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8658381109233/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(8658381109233/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5271/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8658381109233/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(8658381109233/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5271/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8658381109233/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1345469911/10000000000 : ℝ)*X 0 0+(570389107/1000000000 : ℝ)*X 0 1+(4957006247/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1081275891/2000000000 : ℝ)*X 1 0+(-437575959/2500000000 : ℝ)*X 1 1+(991401141/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5406378347/10000000000 : ℝ)*X 2 0+(1239251597/2500000000 : ℝ)*X 2 1+(-437576103/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4042092131/10000000000 : ℝ)*X 0 0+(3057190827/10000000000 : ℝ)*X 0 1+(5207768377/10000000000 : ℝ)*X 0 2+(4042092131/10000000000 : ℝ)*X 1 0+(3057190827/10000000000 : ℝ)*X 1 1+(5207768377/10000000000 : ℝ)*X 1 2+(4042092131/10000000000 : ℝ)*X 2 0+(3057190827/10000000000 : ℝ)*X 2 1+(5207768377/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-269437423/2000000000 : ℝ)*X 0 0+(4975420341/10000000000 : ℝ)*X 0 1+(5684859761/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5203950143/10000000000 : ℝ)*X 1 0+(-1022450093/10000000000 : ℝ)*X 1 1+(355303737/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1040789979/2000000000 : ℝ)*X 2 0+(5684860447/10000000000 : ℝ)*X 2 1+(-1022449469/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2023516231/5000000000 : ℝ)*X 0 0+(5154747397/10000000000 : ℝ)*X 0 1+(3111987067/10000000000 : ℝ)*X 0 2+(2023516231/5000000000 : ℝ)*X 1 0+(5154747397/10000000000 : ℝ)*X 1 1+(3111987067/10000000000 : ℝ)*X 1 2+(2023516231/5000000000 : ℝ)*X 2 0+(5154747397/10000000000 : ℝ)*X 2 1+(3111987067/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((17513403/10000000000 : ℝ)*X 0 0+(2551876093/5000000000 : ℝ)*X 0 1+(1579088253/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_s0_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((690306259/5000000000 : ℝ)*X 1 0+(-3111426057/10000000000 : ℝ)*X 1 1+(183062723/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_s0_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((690307271/5000000000 : ℝ)*X 2 0+(3661256957/5000000000 : ℝ)*X 2 1+(-3111418257/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_s0_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((462790771/2000000000 : ℝ)*X 0 0+(1368928843/2500000000 : ℝ)*X 0 1+(2212247959/5000000000 : ℝ)*X 0 2+(462790771/2000000000 : ℝ)*X 1 0+(1368928843/2500000000 : ℝ)*X 1 1+(2212247959/5000000000 : ℝ)*X 1 2+(462790771/2000000000 : ℝ)*X 2 0+(1368928843/2500000000 : ℝ)*X 2 1+(2212247959/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_s0_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (172385466286897200025281/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (901945720666327/100000000000000 : ℝ)*(major0) + (901945720666327/100000000000000 : ℝ)*(major1) + (901945720666327/100000000000000 : ℝ)*(major2) + (334724202666317/25000000000000 : ℝ)*(sp0) + (669448239970033/50000000000000 : ℝ)*(sp1) + (334724173780689/25000000000000 : ℝ)*(sp2) + (464991802140227/100000000000000 : ℝ)*(sp3) + (808288589/50000000000000 : ℝ)*(sp4) + (372744337/20000000000000 : ℝ)*(sp5) + (1012578613/50000000000000 : ℝ)*(sp6) + (216223/62500000000 : ℝ)*(sp8) + (85907499/20000000000000 : ℝ)*(sp9) + (10583853/20000000000000 : ℝ)*(sp10) + (751069529/100000000000000 : ℝ)*(sp11) + (464992553209757/100000000000000 : ℝ)*(f.failure) + (669449386599623/50000000000000 : ℝ)*(f.sum) + (191400550497191/100000000000000000000000000000 : ℝ)*base65 + (1325602776897191/200000000000000000000000000000 : ℝ)*base67 + (1779576240897191/200000000000000000000000000000 : ℝ)*base69 + (1532563046497191/200000000000000000000000000000 : ℝ)*base71 + (148699089797191/100000000000000000000000000000 : ℝ)*base73 + (1939561001697191/200000000000000000000000000000 : ℝ)*base75 + (574873079097191/200000000000000000000000000000 : ℝ)*base77 + (150110916497191/200000000000000000000000000000 : ℝ)*base79 + (475617068897191/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (4273437/1250000000000000000000 : ℝ)*base89 + (4273437/1250000000000000000000 : ℝ)*base91 + (4273437/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (146442293534506699698447/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (949549027860347/100000000000000 : ℝ)*(major0) + (949549027860347/100000000000000 : ℝ)*(major1) + (949549027860347/100000000000000 : ℝ)*(major2) + (130059461/20000000000000 : ℝ)*(sp0) + (1246346929/100000000000000 : ℝ)*(sp2) + (35073769/50000000000000 : ℝ)*(sp3) + (281912299412687/20000000000000 : ℝ)*(sp4) + (704781743354627/50000000000000 : ℝ)*(sp5) + (352390566451193/25000000000000 : ℝ)*(sp6) + (244766729078479/50000000000000 : ℝ)*(sp7) + (416527227/25000000000000 : ℝ)*(sp8) + (163380197/50000000000000 : ℝ)*(sp9) + (301317947/100000000000000 : ℝ)*(sp10) + (154079587/25000000000000 : ℝ)*(sp11) + (122383536155711/25000000000000 : ℝ)*(f.failure) + (88097738341853/6250000000000 : ℝ)*(f.sum) + (15320489516149/100000000000000000000000000000 : ℝ)*base66 + (990600820083851/200000000000000000000000000000 : ℝ)*base67 + (999797327883851/200000000000000000000000000000 : ℝ)*base69 + (1061366270683851/200000000000000000000000000000 : ℝ)*base71 + (161681413483851/100000000000000000000000000000 : ℝ)*base73 + (945278251483851/200000000000000000000000000000 : ℝ)*base75 + (414667238083851/200000000000000000000000000000 : ℝ)*base77 + (1248744915883851/200000000000000000000000000000 : ℝ)*base79 + (194861151816149/100000000000000000000000000000 : ℝ)*base82 + (1942649/312500000000000000000 : ℝ)*base90 + (1942649/312500000000000000000 : ℝ)*base92 + (1942649/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1707_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24246241/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5963/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (11007/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1707_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1707_s1_0 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-354778657/2500000000 : ℝ)*x 0 + (2743875273/5000000000 : ℝ)*x 1 + (5124707961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (354778657/2500000000 : ℝ)^5279 ≤ (8870409242439/100000000000000 : ℝ)^4255 := by
    have hnat : (354778657 : ℕ)^5279*100000000000000^4255 ≤ 8870409242439^4255*2500000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      354778657 2500000000 8870409242439 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2743875273/5000000000 : ℝ)^5279 ≤ (148431999823/312500000000 : ℝ)^4255 := by
    have hnat : (2743875273 : ℕ)^5279*312500000000^4255 ≤ 148431999823^4255*5000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2743875273 5000000000 148431999823 312500000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5124707961/10000000000 : ℝ)^5279 ≤ (43631350795657/100000000000000 : ℝ)^4255 := by
    have hnat : (5124707961 : ℕ)^5279*100000000000000^4255 ≤ 43631350795657^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5124707961 10000000000 43631350795657 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-354778657/2500000000 : ℝ), (2743875273/5000000000 : ℝ), (5124707961/10000000000 : ℝ)] ![(8870409242439/100000000000000 : ℝ), (148431999823/312500000000 : ℝ), (43631350795657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-354778657/2500000000 : ℝ)|^5279 ≤ (8870409242439/100000000000000 : ℝ)^4255
        have hw : |(-354778657/2500000000 : ℝ)|=(354778657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2743875273/5000000000 : ℝ)|^5279 ≤ (148431999823/312500000000 : ℝ)^4255
        have hw : |(2743875273/5000000000 : ℝ)|=(2743875273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5124707961/10000000000 : ℝ)|^5279 ≤ (43631350795657/100000000000000 : ℝ)^4255
        have hw : |(5124707961/10000000000 : ℝ)|=(5124707961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_s1_1 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668600367/1250000000 : ℝ)*x 0 + (-1607998423/10000000000 : ℝ)*x 1 + (1024941413/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668600367/1250000000 : ℝ)^5279 ≤ (23005377539587/50000000000000 : ℝ)^4255 := by
    have hnat : (668600367 : ℕ)^5279*50000000000000^4255 ≤ 23005377539587^4255*1250000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668600367 1250000000 23005377539587 50000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1607998423/10000000000 : ℝ)^5279 ≤ (10357903574433/100000000000000 : ℝ)^4255 := by
    have hnat : (1607998423 : ℕ)^5279*100000000000000^4255 ≤ 10357903574433^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1607998423 10000000000 10357903574433 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1024941413/2000000000 : ℝ)^5279 ≤ (10907835332833/25000000000000 : ℝ)^4255 := by
    have hnat : (1024941413 : ℕ)^5279*25000000000000^4255 ≤ 10907835332833^4255*2000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024941413 2000000000 10907835332833 25000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668600367/1250000000 : ℝ), (-1607998423/10000000000 : ℝ), (1024941413/2000000000 : ℝ)] ![(23005377539587/50000000000000 : ℝ), (10357903574433/100000000000000 : ℝ), (10907835332833/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668600367/1250000000 : ℝ)|^5279 ≤ (23005377539587/50000000000000 : ℝ)^4255
        have hw : |(668600367/1250000000 : ℝ)|=(668600367/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1607998423/10000000000 : ℝ)|^5279 ≤ (10357903574433/100000000000000 : ℝ)^4255
        have hw : |(-1607998423/10000000000 : ℝ)|=(1607998423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1024941413/2000000000 : ℝ)|^5279 ≤ (10907835332833/25000000000000 : ℝ)^4255
        have hw : |(1024941413/2000000000 : ℝ)|=(1024941413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_s1_2 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348801557/10000000000 : ℝ)*x 0 + (2562354133/5000000000 : ℝ)*x 1 + (-1607998677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348801557/10000000000 : ℝ)^5279 ≤ (2300537018109/5000000000000 : ℝ)^4255 := by
    have hnat : (5348801557 : ℕ)^5279*5000000000000^4255 ≤ 2300537018109^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348801557 10000000000 2300537018109 5000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2562354133/5000000000 : ℝ)^5279 ≤ (4363135401733/10000000000000 : ℝ)^4255 := by
    have hnat : (2562354133 : ℕ)^5279*10000000000000^4255 ≤ 4363135401733^4255*5000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2562354133 5000000000 4363135401733 10000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1607998677/10000000000 : ℝ)^5279 ≤ (10357905604321/100000000000000 : ℝ)^4255 := by
    have hnat : (1607998677 : ℕ)^5279*100000000000000^4255 ≤ 10357905604321^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1607998677 10000000000 10357905604321 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348801557/10000000000 : ℝ), (2562354133/5000000000 : ℝ), (-1607998677/10000000000 : ℝ)] ![(2300537018109/5000000000000 : ℝ), (4363135401733/10000000000000 : ℝ), (10357905604321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348801557/10000000000 : ℝ)|^5279 ≤ (2300537018109/5000000000000 : ℝ)^4255
        have hw : |(5348801557/10000000000 : ℝ)|=(5348801557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2562354133/5000000000 : ℝ)|^5279 ≤ (4363135401733/10000000000000 : ℝ)^4255
        have hw : |(2562354133/5000000000 : ℝ)|=(2562354133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1607998677/10000000000 : ℝ)|^5279 ≤ (10357905604321/100000000000000 : ℝ)^4255
        have hw : |(-1607998677/10000000000 : ℝ)|=(1607998677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_s1_3 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1026397583/2500000000 : ℝ)*x 0 + (56314329/156250000 : ℝ)*x 1 + (4649460449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1026397583/2500000000 : ℝ)^5279 ≤ (8284596282583/25000000000000 : ℝ)^4255 := by
    have hnat : (1026397583 : ℕ)^5279*25000000000000^4255 ≤ 8284596282583^4255*2500000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026397583 2500000000 8284596282583 25000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56314329/156250000 : ℝ)^5279 ≤ (28192849473897/100000000000000 : ℝ)^4255 := by
    have hnat : (56314329 : ℕ)^5279*100000000000000^4255 ≤ 28192849473897^4255*156250000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56314329 156250000 28192849473897 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4649460449/10000000000 : ℝ)^5279 ≤ (38668765372977/100000000000000 : ℝ)^4255 := by
    have hnat : (4649460449 : ℕ)^5279*100000000000000^4255 ≤ 38668765372977^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4649460449 10000000000 38668765372977 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1026397583/2500000000 : ℝ), (56314329/156250000 : ℝ), (4649460449/10000000000 : ℝ)] ![(8284596282583/25000000000000 : ℝ), (28192849473897/100000000000000 : ℝ), (38668765372977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1026397583/2500000000 : ℝ)|^5279 ≤ (8284596282583/25000000000000 : ℝ)^4255
        have hw : |(1026397583/2500000000 : ℝ)|=(1026397583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(56314329/156250000 : ℝ)|^5279 ≤ (28192849473897/100000000000000 : ℝ)^4255
        have hw : |(56314329/156250000 : ℝ)|=(56314329/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4649460449/10000000000 : ℝ)|^5279 ≤ (38668765372977/100000000000000 : ℝ)^4255
        have hw : |(4649460449/10000000000 : ℝ)|=(4649460449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_s1_4 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-11088363/78125000 : ℝ)*x 0 + (5129062421/10000000000 : ℝ)*x 1 + (5483324927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (11088363/78125000 : ℝ)^5279 ≤ (1108990995439/12500000000000 : ℝ)^4255 := by
    have hnat : (11088363 : ℕ)^5279*12500000000000^4255 ≤ 1108990995439^4255*78125000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11088363 78125000 1108990995439 12500000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5129062421/10000000000 : ℝ)^5279 ≤ (5459668882563/12500000000000 : ℝ)^4255 := by
    have hnat : (5129062421 : ℕ)^5279*12500000000000^4255 ≤ 5459668882563^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129062421 10000000000 5459668882563 12500000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5483324927/10000000000 : ℝ)^5279 ≤ (23725360481049/50000000000000 : ℝ)^4255 := by
    have hnat : (5483324927 : ℕ)^5279*50000000000000^4255 ≤ 23725360481049^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5483324927 10000000000 23725360481049 50000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-11088363/78125000 : ℝ), (5129062421/10000000000 : ℝ), (5483324927/10000000000 : ℝ)] ![(1108990995439/12500000000000 : ℝ), (5459668882563/12500000000000 : ℝ), (23725360481049/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-11088363/78125000 : ℝ)|^5279 ≤ (1108990995439/12500000000000 : ℝ)^4255
        have hw : |(-11088363/78125000 : ℝ)|=(11088363/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5129062421/10000000000 : ℝ)|^5279 ≤ (5459668882563/12500000000000 : ℝ)^4255
        have hw : |(5129062421/10000000000 : ℝ)|=(5129062421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5483324927/10000000000 : ℝ)|^5279 ≤ (23725360481049/50000000000000 : ℝ)^4255
        have hw : |(5483324927/10000000000 : ℝ)|=(5483324927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_s1_5 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625797021/5000000000 : ℝ)*x 0 + (-1249380707/10000000000 : ℝ)*x 1 + (5483324607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625797021/5000000000 : ℝ)^5279 ≤ (44975599398121/100000000000000 : ℝ)^4255 := by
    have hnat : (2625797021 : ℕ)^5279*100000000000000^4255 ≤ 44975599398121^4255*5000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625797021 5000000000 44975599398121 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1249380707/10000000000 : ℝ)^5279 ≤ (378684152749/5000000000000 : ℝ)^4255 := by
    have hnat : (1249380707 : ℕ)^5279*5000000000000^4255 ≤ 378684152749^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1249380707 10000000000 378684152749 5000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5483324607/10000000000 : ℝ)^5279 ≤ (2965669845407/6250000000000 : ℝ)^4255 := by
    have hnat : (5483324607 : ℕ)^5279*6250000000000^4255 ≤ 2965669845407^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5483324607 10000000000 2965669845407 6250000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625797021/5000000000 : ℝ), (-1249380707/10000000000 : ℝ), (5483324607/10000000000 : ℝ)] ![(44975599398121/100000000000000 : ℝ), (378684152749/5000000000000 : ℝ), (2965669845407/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625797021/5000000000 : ℝ)|^5279 ≤ (44975599398121/100000000000000 : ℝ)^4255
        have hw : |(2625797021/5000000000 : ℝ)|=(2625797021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1249380707/10000000000 : ℝ)|^5279 ≤ (378684152749/5000000000000 : ℝ)^4255
        have hw : |(-1249380707/10000000000 : ℝ)|=(1249380707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5483324607/10000000000 : ℝ)|^5279 ≤ (2965669845407/6250000000000 : ℝ)^4255
        have hw : |(5483324607/10000000000 : ℝ)|=(5483324607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_s1_6 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (525159353/1000000000 : ℝ)*x 0 + (2741662149/5000000000 : ℝ)*x 1 + (-1249381873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525159353/1000000000 : ℝ)^5279 ≤ (44975593958009/100000000000000 : ℝ)^4255 := by
    have hnat : (525159353 : ℕ)^5279*100000000000000^4255 ≤ 44975593958009^4255*1000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525159353 1000000000 44975593958009 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2741662149/5000000000 : ℝ)^5279 ≤ (47450714209023/100000000000000 : ℝ)^4255 := by
    have hnat : (2741662149 : ℕ)^5279*100000000000000^4255 ≤ 47450714209023^4255*5000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2741662149 5000000000 47450714209023 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1249381873/10000000000 : ℝ)^5279 ≤ (3786845912121/50000000000000 : ℝ)^4255 := by
    have hnat : (1249381873 : ℕ)^5279*50000000000000^4255 ≤ 3786845912121^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1249381873 10000000000 3786845912121 50000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525159353/1000000000 : ℝ), (2741662149/5000000000 : ℝ), (-1249381873/10000000000 : ℝ)] ![(44975593958009/100000000000000 : ℝ), (47450714209023/100000000000000 : ℝ), (3786845912121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525159353/1000000000 : ℝ)|^5279 ≤ (44975593958009/100000000000000 : ℝ)^4255
        have hw : |(525159353/1000000000 : ℝ)|=(525159353/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2741662149/5000000000 : ℝ)|^5279 ≤ (47450714209023/100000000000000 : ℝ)^4255
        have hw : |(2741662149/5000000000 : ℝ)|=(2741662149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1249381873/10000000000 : ℝ)|^5279 ≤ (3786845912121/50000000000000 : ℝ)^4255
        have hw : |(-1249381873/10000000000 : ℝ)|=(1249381873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_s1_7 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4106152533/10000000000 : ℝ)*x 0 + (4636921493/10000000000 : ℝ)*x 1 + (1808429349/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4106152533/10000000000 : ℝ)^5279 ≤ (8286003776753/25000000000000 : ℝ)^4255 := by
    have hnat : (4106152533 : ℕ)^5279*25000000000000^4255 ≤ 8286003776753^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4106152533 10000000000 8286003776753 25000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4636921493/10000000000 : ℝ)^5279 ≤ (9634856543137/25000000000000 : ℝ)^4255 := by
    have hnat : (4636921493 : ℕ)^5279*25000000000000^4255 ≤ 9634856543137^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4636921493 10000000000 9634856543137 25000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1808429349/5000000000 : ℝ)^5279 ≤ (1769784919379/6250000000000 : ℝ)^4255 := by
    have hnat : (1808429349 : ℕ)^5279*6250000000000^4255 ≤ 1769784919379^4255*5000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1808429349 5000000000 1769784919379 6250000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4106152533/10000000000 : ℝ), (4636921493/10000000000 : ℝ), (1808429349/5000000000 : ℝ)] ![(8286003776753/25000000000000 : ℝ), (9634856543137/25000000000000 : ℝ), (1769784919379/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4106152533/10000000000 : ℝ)|^5279 ≤ (8286003776753/25000000000000 : ℝ)^4255
        have hw : |(4106152533/10000000000 : ℝ)|=(4106152533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4636921493/10000000000 : ℝ)|^5279 ≤ (9634856543137/25000000000000 : ℝ)^4255
        have hw : |(4636921493/10000000000 : ℝ)|=(4636921493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1808429349/5000000000 : ℝ)|^5279 ≤ (1769784919379/6250000000000 : ℝ)^4255
        have hw : |(1808429349/5000000000 : ℝ)|=(1808429349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1707_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24246241/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11007/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5963/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4849/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8723/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (11007/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5963/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (11007/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5963/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (11007/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5963/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (11007/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5963/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (11007/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5963/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (11007/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5963/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5963/100000 : ℝ) ^ (5271/1024 : ℝ) ≤ (49745401392797/100000000000000000000 : ℝ) := by
    have hpowers : (5963/100000 : ℝ)^5271 ≤ (49745401392797/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5963 : ℕ)^5271*100000000000000000000^1024 ≤ 49745401392797^1024*100000^5271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5963 100000 49745401392797 100000000000000000000 5271 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5963/100000 : ℝ)) (X := (49745401392797/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5271 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (11007/50000 : ℝ) ^ (5271/1024 : ℝ) ≤ (10339715569336473/25000000000000000000 : ℝ) := by
    have hpowers : (11007/50000 : ℝ)^5271 ≤ (10339715569336473/25000000000000000000 : ℝ)^1024 := by
      have hnat : (11007 : ℕ)^5271*25000000000000000000^1024 ≤ 10339715569336473^1024*50000^5271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11007 50000 10339715569336473 25000000000000000000 5271 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11007/50000 : ℝ)) (X := (10339715569336473/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5271 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000049745401392797/50000000000000000000 : ℝ) ≤ (10000001932812393/10000000000000000 : ℝ) ^ (5271/1024 : ℝ) := by
    have hpowers : (50000049745401392797/50000000000000000000 : ℝ)^1024 ≤ (10000001932812393/10000000000000000 : ℝ)^5271 := by
      have hnat : (50000049745401392797 : ℕ)^1024*10000000000000000^5271 ≤ 10000001932812393^5271*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000049745401392797 50000000000000000000 10000001932812393 10000000000000000 1024 5271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001932812393/10000000000000000 : ℝ)) (X := (50000049745401392797/50000000000000000000 : ℝ)) (by norm_num) 5271 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100041408607678738689/100000000000000000000 : ℝ) ≤ (10000804313079609/10000000000000000 : ℝ) ^ (5271/1024 : ℝ) := by
    have hpowers : (100041408607678738689/100000000000000000000 : ℝ)^1024 ≤ (10000804313079609/10000000000000000 : ℝ)^5271 := by
      have hnat : (100041408607678738689 : ℕ)^1024*10000000000000000^5271 ≤ 10000804313079609^5271*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100041408607678738689 100000000000000000000 10000804313079609 10000000000000000 1024 5271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000804313079609/10000000000000000 : ℝ)) (X := (100041408607678738689/100000000000000000000 : ℝ)) (by norm_num) 5271 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12510339715569336473/12500000000000000000 : ℝ) ≤ (400064267733873/400000000000000 : ℝ) ^ (5271/1024 : ℝ) := by
    have hpowers : (12510339715569336473/12500000000000000000 : ℝ)^1024 ≤ (400064267733873/400000000000000 : ℝ)^5271 := by
      have hnat : (12510339715569336473 : ℕ)^1024*400000000000000^5271 ≤ 400064267733873^5271*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12510339715569336473 12500000000000000000 400064267733873 400000000000000 1024 5271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400064267733873/400000000000000 : ℝ)) (X := (12510339715569336473/12500000000000000000 : ℝ)) (by norm_num) 5271 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(49745401392797/100000000000000000000 : ℝ) ≤ ((160500461836504902027/160510000000000000000 : ℝ)+2*(50148766701/100318750000000 : ℝ)*(5963/100000 : ℝ))^(5271/1024 : ℝ) := by
    rw [show (160500461836504902027/160510000000000000000 : ℝ)+2*(50148766701/100318750000000 : ℝ)*(5963/100000 : ℝ)=(10000001932812393/10000000000000000 : ℝ) by norm_num, show 1+2*(49745401392797/100000000000000000000 : ℝ)=(50000049745401392797/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10339715569336473/25000000000000000000 : ℝ)+(49745401392797/100000000000000000000 : ℝ) ≤ ((160500461836504902027/160510000000000000000 : ℝ)+(50148766701/100318750000000 : ℝ)*((11007/50000 : ℝ)+(5963/100000 : ℝ)))^(5271/1024 : ℝ) := by
    rw [show (160500461836504902027/160510000000000000000 : ℝ)+(50148766701/100318750000000 : ℝ)*((11007/50000 : ℝ)+(5963/100000 : ℝ))=(10000804313079609/10000000000000000 : ℝ) by norm_num, show 1+(10339715569336473/25000000000000000000 : ℝ)+(49745401392797/100000000000000000000 : ℝ)=(100041408607678738689/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10339715569336473/25000000000000000000 : ℝ) ≤ ((160500461836504902027/160510000000000000000 : ℝ)+2*(50148766701/100318750000000 : ℝ)*(11007/50000 : ℝ))^(5271/1024 : ℝ) := by
    rw [show (160500461836504902027/160510000000000000000 : ℝ)+2*(50148766701/100318750000000 : ℝ)*(11007/50000 : ℝ)=(400064267733873/400000000000000 : ℝ) by norm_num, show 1+2*(10339715569336473/25000000000000000000 : ℝ)=(12510339715569336473/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (160500461836504902027/160510000000000000000 : ℝ)*(X 1 0+X 2 0)+(50148766701/100318750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5271/1024 : ℝ)) (lo := (5963/100000 : ℝ)) (hi := (11007/50000 : ℝ)) (c := (160500461836504902027/160510000000000000000 : ℝ)) (alpha := (50148766701/100318750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (160500461836504902027/160510000000000000000 : ℝ)*(X 0 1+X 2 1)+(50148766701/100318750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5271/1024 : ℝ)) (lo := (5963/100000 : ℝ)) (hi := (11007/50000 : ℝ)) (c := (160500461836504902027/160510000000000000000 : ℝ)) (alpha := (50148766701/100318750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (160500461836504902027/160510000000000000000 : ℝ)*(X 0 2+X 1 2)+(50148766701/100318750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5271/1024 : ℝ)) (lo := (5963/100000 : ℝ)) (hi := (11007/50000 : ℝ)) (c := (160500461836504902027/160510000000000000000 : ℝ)) (alpha := (50148766701/100318750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-354778657/2500000000 : ℝ)*X 0 0+(2743875273/5000000000 : ℝ)*X 0 1+(5124707961/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668600367/1250000000 : ℝ)*X 1 0+(-1607998423/10000000000 : ℝ)*X 1 1+(1024941413/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348801557/10000000000 : ℝ)*X 2 0+(2562354133/5000000000 : ℝ)*X 2 1+(-1607998677/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1026397583/2500000000 : ℝ)*X 0 0+(56314329/156250000 : ℝ)*X 0 1+(4649460449/10000000000 : ℝ)*X 0 2+(1026397583/2500000000 : ℝ)*X 1 0+(56314329/156250000 : ℝ)*X 1 1+(4649460449/10000000000 : ℝ)*X 1 2+(1026397583/2500000000 : ℝ)*X 2 0+(56314329/156250000 : ℝ)*X 2 1+(4649460449/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-11088363/78125000 : ℝ)*X 0 0+(5129062421/10000000000 : ℝ)*X 0 1+(5483324927/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2625797021/5000000000 : ℝ)*X 1 0+(-1249380707/10000000000 : ℝ)*X 1 1+(5483324607/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((525159353/1000000000 : ℝ)*X 2 0+(2741662149/5000000000 : ℝ)*X 2 1+(-1249381873/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4106152533/10000000000 : ℝ)*X 0 0+(4636921493/10000000000 : ℝ)*X 0 1+(1808429349/5000000000 : ℝ)*X 0 2+(4106152533/10000000000 : ℝ)*X 1 0+(4636921493/10000000000 : ℝ)*X 1 1+(1808429349/5000000000 : ℝ)*X 1 2+(4106152533/10000000000 : ℝ)*X 2 0+(4636921493/10000000000 : ℝ)*X 2 1+(1808429349/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (539206847074889115867069/40127500000000000000000000000 : ℝ) := by norm_num
    linear_combination (428165711/25000000000000 : ℝ)*(base19) + (55498451/6250000000000 : ℝ)*(base23) + (101928749/100000000000000 : ℝ)*(lower2) + (86606307/25000000000000 : ℝ)*(upper3) + (20333797/50000000000000 : ℝ)*(lower4) + (1855574588022999/100000000000000 : ℝ)*(major0) + (1855574588022999/100000000000000 : ℝ)*(major1) + (1855574588022999/100000000000000 : ℝ)*(major2) + (172156997076713/6250000000000 : ℝ)*(sp0) + (1377258490775399/50000000000000 : ℝ)*(sp1) + (1377258903119213/50000000000000 : ℝ)*(sp2) + (119578250464339/12500000000000 : ℝ)*(sp3) + (3370493117/50000000000000 : ℝ)*(sp4) + (4030206319/100000000000000 : ℝ)*(sp7) + (956630033921031/100000000000000 : ℝ)*(f.failure) + (1377259347106821/50000000000000 : ℝ)*(f.sum) + (307436957199979/80255000000000000000000000000 : ℝ)*base65 + (10251417127182125861/2293000000000000000000000000000000 : ℝ)*base68 + (2295491504862874139/2293000000000000000000000000000000 : ℝ)*base69 + (11900925868843874139/2293000000000000000000000000000000 : ℝ)*base71 + (57410857998391/80255000000000000000000000000 : ℝ)*base74 + (2955336017289125861/2293000000000000000000000000000000 : ℝ)*base76 + (9317892659121874139/2293000000000000000000000000000000 : ℝ)*base77 + (10451256741144125861/2293000000000000000000000000000000 : ℝ)*base80 + (38131540248511/20063750000000000000000000000 : ℝ)*base81 + (5094471/1250000000000000000000 : ℝ)*base89 + (5094471/1250000000000000000000 : ℝ)*base91 + (5094471/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4358214547979470322645282469/573250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1563599217/100000000000000 : ℝ)*(base19) + (1216476249/100000000000000 : ℝ)*(base23) + (12176411/25000000000000 : ℝ)*(upper2) + (182025887/100000000000000 : ℝ)*(upper3) + (195880013/100000000000000 : ℝ)*(upper5) + (1901547613871843/100000000000000 : ℝ)*(major0) + (1901547613871843/100000000000000 : ℝ)*(major1) + (1901547613871843/100000000000000 : ℝ)*(major2) + (483939161/4000000000000 : ℝ)*(sp1) + (640541497/20000000000000 : ℝ)*(sp2) + (2822763830480311/100000000000000 : ℝ)*(sp4) + (2822750168402069/100000000000000 : ℝ)*(sp5) + (44105615801509/1562500000000 : ℝ)*(sp6) + (980331143841969/100000000000000 : ℝ)*(sp7) + (980331143841969/100000000000000 : ℝ)*(f.failure) + (2822763830480311/100000000000000 : ℝ)*(f.sum) + (50879313592861/11465000000000000000000000000 : ℝ)*base66 + (2015322305470039177/2293000000000000000000000000000000 : ℝ)*base68 + (1894426198693039177/2293000000000000000000000000000000 : ℝ)*base70 + (13016483091681039177/2293000000000000000000000000000000 : ℝ)*base72 + (53306624634649/11465000000000000000000000000 : ℝ)*base73 + (7168810505516039177/2293000000000000000000000000000000 : ℝ)*base76 + (7378035363892039177/2293000000000000000000000000000000 : ℝ)*base78 + (8775348294518960823/2293000000000000000000000000000000 : ℝ)*base79 + (44017076167999/11465000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (8788529/1250000000000000000000 : ℝ)*base89 + (8788529/1250000000000000000000 : ℝ)*base91 + (8788529/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1707_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24246241/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11007/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5963/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4849/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8723/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1707_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1707_s2_0 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-711417729/5000000000 : ℝ)*x 0 + (2736273307/5000000000 : ℝ)*x 1 + (5137422871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (711417729/5000000000 : ℝ)^5279 ≤ (1779854628487/20000000000000 : ℝ)^4255 := by
    have hnat : (711417729 : ℕ)^5279*20000000000000^4255 ≤ 1779854628487^4255*5000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      711417729 5000000000 1779854628487 20000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2736273307/5000000000 : ℝ)^5279 ≤ (11833757532969/25000000000000 : ℝ)^4255 := by
    have hnat : (2736273307 : ℕ)^5279*25000000000000^4255 ≤ 11833757532969^4255*5000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2736273307 5000000000 11833757532969 25000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5137422871/10000000000 : ℝ)^5279 ≤ (43765696715853/100000000000000 : ℝ)^4255 := by
    have hnat : (5137422871 : ℕ)^5279*100000000000000^4255 ≤ 43765696715853^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5137422871 10000000000 43765696715853 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-711417729/5000000000 : ℝ), (2736273307/5000000000 : ℝ), (5137422871/10000000000 : ℝ)] ![(1779854628487/20000000000000 : ℝ), (11833757532969/25000000000000 : ℝ), (43765696715853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-711417729/5000000000 : ℝ)|^5279 ≤ (1779854628487/20000000000000 : ℝ)^4255
        have hw : |(-711417729/5000000000 : ℝ)|=(711417729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2736273307/5000000000 : ℝ)|^5279 ≤ (11833757532969/25000000000000 : ℝ)^4255
        have hw : |(2736273307/5000000000 : ℝ)|=(2736273307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5137422871/10000000000 : ℝ)|^5279 ≤ (43765696715853/100000000000000 : ℝ)^4255
        have hw : |(5137422871/10000000000 : ℝ)|=(5137422871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_s2_1 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344689009/10000000000 : ℝ)*x 0 + (-319334071/2000000000 : ℝ)*x 1 + (2568711377/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344689009/10000000000 : ℝ)^5279 ≤ (22983427200037/50000000000000 : ℝ)^4255 := by
    have hnat : (5344689009 : ℕ)^5279*50000000000000^4255 ≤ 22983427200037^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344689009 10000000000 22983427200037 50000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (319334071/2000000000 : ℝ)^5279 ≤ (10267450105939/100000000000000 : ℝ)^4255 := by
    have hnat : (319334071 : ℕ)^5279*100000000000000^4255 ≤ 10267450105939^4255*2000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319334071 2000000000 10267450105939 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2568711377/5000000000 : ℝ)^5279 ≤ (43765695479261/100000000000000 : ℝ)^4255 := by
    have hnat : (2568711377 : ℕ)^5279*100000000000000^4255 ≤ 43765695479261^4255*5000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2568711377 5000000000 43765695479261 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344689009/10000000000 : ℝ), (-319334071/2000000000 : ℝ), (2568711377/5000000000 : ℝ)] ![(22983427200037/50000000000000 : ℝ), (10267450105939/100000000000000 : ℝ), (43765695479261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344689009/10000000000 : ℝ)|^5279 ≤ (22983427200037/50000000000000 : ℝ)^4255
        have hw : |(5344689009/10000000000 : ℝ)|=(5344689009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-319334071/2000000000 : ℝ)|^5279 ≤ (10267450105939/100000000000000 : ℝ)^4255
        have hw : |(-319334071/2000000000 : ℝ)|=(319334071/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2568711377/5000000000 : ℝ)|^5279 ≤ (43765695479261/100000000000000 : ℝ)^4255
        have hw : |(2568711377/5000000000 : ℝ)|=(2568711377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_s2_2 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344689013/10000000000 : ℝ)*x 0 + (5137422803/10000000000 : ℝ)*x 1 + (-319334057/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344689013/10000000000 : ℝ)^5279 ≤ (9193370888551/20000000000000 : ℝ)^4255 := by
    have hnat : (5344689013 : ℕ)^5279*20000000000000^4255 ≤ 9193370888551^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344689013 10000000000 9193370888551 20000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5137422803/10000000000 : ℝ)^5279 ≤ (875313919943/2000000000000 : ℝ)^4255 := by
    have hnat : (5137422803 : ℕ)^5279*2000000000000^4255 ≤ 875313919943^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5137422803 10000000000 875313919943 2000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (319334057/2000000000 : ℝ)^5279 ≤ (641715596717/6250000000000 : ℝ)^4255 := by
    have hnat : (319334057 : ℕ)^5279*6250000000000^4255 ≤ 641715596717^4255*2000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319334057 2000000000 641715596717 6250000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344689013/10000000000 : ℝ), (5137422803/10000000000 : ℝ), (-319334057/2000000000 : ℝ)] ![(9193370888551/20000000000000 : ℝ), (875313919943/2000000000000 : ℝ), (641715596717/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344689013/10000000000 : ℝ)|^5279 ≤ (9193370888551/20000000000000 : ℝ)^4255
        have hw : |(5344689013/10000000000 : ℝ)|=(5344689013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5137422803/10000000000 : ℝ)|^5279 ≤ (875313919943/2000000000000 : ℝ)^4255
        have hw : |(5137422803/10000000000 : ℝ)|=(5137422803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-319334057/2000000000 : ℝ)|^5279 ≤ (641715596717/6250000000000 : ℝ)^4255
        have hw : |(-319334057/2000000000 : ℝ)|=(319334057/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_s2_3 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4108470187/10000000000 : ℝ)*x 0 + (227753413/625000000 : ℝ)*x 1 + (576126201/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4108470187/10000000000 : ℝ)^5279 ≤ (16583613223951/50000000000000 : ℝ)^4255 := by
    have hnat : (4108470187 : ℕ)^5279*50000000000000^4255 ≤ 16583613223951^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4108470187 10000000000 16583613223951 50000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (227753413/625000000 : ℝ)^5279 ≤ (2858095578213/10000000000000 : ℝ)^4255 := by
    have hnat : (227753413 : ℕ)^5279*10000000000000^4255 ≤ 2858095578213^4255*625000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227753413 625000000 2858095578213 10000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (576126201/1250000000 : ℝ)^5279 ≤ (38251817748013/100000000000000 : ℝ)^4255 := by
    have hnat : (576126201 : ℕ)^5279*100000000000000^4255 ≤ 38251817748013^4255*1250000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      576126201 1250000000 38251817748013 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4108470187/10000000000 : ℝ), (227753413/625000000 : ℝ), (576126201/1250000000 : ℝ)] ![(16583613223951/50000000000000 : ℝ), (2858095578213/10000000000000 : ℝ), (38251817748013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4108470187/10000000000 : ℝ)|^5279 ≤ (16583613223951/50000000000000 : ℝ)^4255
        have hw : |(4108470187/10000000000 : ℝ)|=(4108470187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(227753413/625000000 : ℝ)|^5279 ≤ (2858095578213/10000000000000 : ℝ)^4255
        have hw : |(227753413/625000000 : ℝ)|=(227753413/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(576126201/1250000000 : ℝ)|^5279 ≤ (38251817748013/100000000000000 : ℝ)^4255
        have hw : |(576126201/1250000000 : ℝ)|=(576126201/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_s2_4 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-711494503/5000000000 : ℝ)*x 0 + (2570568121/5000000000 : ℝ)*x 1 + (5468777623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (711494503/5000000000 : ℝ)^5279 ≤ (8900464663591/100000000000000 : ℝ)^4255 := by
    have hnat : (711494503 : ℕ)^5279*100000000000000^4255 ≤ 8900464663591^4255*5000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      711494503 5000000000 8900464663591 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2570568121/5000000000 : ℝ)^5279 ≤ (21902473677579/50000000000000 : ℝ)^4255 := by
    have hnat : (2570568121 : ℕ)^5279*50000000000000^4255 ≤ 21902473677579^4255*5000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2570568121 5000000000 21902473677579 50000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5468777623/10000000000 : ℝ)^5279 ≤ (9458917593539/20000000000000 : ℝ)^4255 := by
    have hnat : (5468777623 : ℕ)^5279*20000000000000^4255 ≤ 9458917593539^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468777623 10000000000 9458917593539 20000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-711494503/5000000000 : ℝ), (2570568121/5000000000 : ℝ), (5468777623/10000000000 : ℝ)] ![(8900464663591/100000000000000 : ℝ), (21902473677579/50000000000000 : ℝ), (9458917593539/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-711494503/5000000000 : ℝ)|^5279 ≤ (8900464663591/100000000000000 : ℝ)^4255
        have hw : |(-711494503/5000000000 : ℝ)|=(711494503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2570568121/5000000000 : ℝ)|^5279 ≤ (21902473677579/50000000000000 : ℝ)^4255
        have hw : |(2570568121/5000000000 : ℝ)|=(2570568121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5468777623/10000000000 : ℝ)|^5279 ≤ (9458917593539/20000000000000 : ℝ)^4255
        have hw : |(5468777623/10000000000 : ℝ)|=(5468777623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_s2_5 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (328436987/625000000 : ℝ)*x 0 + (-316328859/2500000000 : ℝ)*x 1 + (5468777583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328436987/625000000 : ℝ)^5279 ≤ (45011704047821/100000000000000 : ℝ)^4255 := by
    have hnat : (328436987 : ℕ)^5279*100000000000000^4255 ≤ 45011704047821^4255*625000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328436987 625000000 45011704047821 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (316328859/2500000000 : ℝ)^5279 ≤ (192342710051/2500000000000 : ℝ)^4255 := by
    have hnat : (316328859 : ℕ)^5279*2500000000000^4255 ≤ 192342710051^4255*2500000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      316328859 2500000000 192342710051 2500000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5468777583/10000000000 : ℝ)^5279 ≤ (47294587538521/100000000000000 : ℝ)^4255 := by
    have hnat : (5468777583 : ℕ)^5279*100000000000000^4255 ≤ 47294587538521^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468777583 10000000000 47294587538521 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328436987/625000000 : ℝ), (-316328859/2500000000 : ℝ), (5468777583/10000000000 : ℝ)] ![(45011704047821/100000000000000 : ℝ), (192342710051/2500000000000 : ℝ), (47294587538521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328436987/625000000 : ℝ)|^5279 ≤ (45011704047821/100000000000000 : ℝ)^4255
        have hw : |(328436987/625000000 : ℝ)|=(328436987/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-316328859/2500000000 : ℝ)|^5279 ≤ (192342710051/2500000000000 : ℝ)^4255
        have hw : |(-316328859/2500000000 : ℝ)|=(316328859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5468777583/10000000000 : ℝ)|^5279 ≤ (47294587538521/100000000000000 : ℝ)^4255
        have hw : |(5468777583/10000000000 : ℝ)|=(5468777583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_s2_6 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2627495863/5000000000 : ℝ)*x 0 + (546877759/1000000000 : ℝ)*x 1 + (-1265315519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2627495863/5000000000 : ℝ)^5279 ≤ (2813231459153/6250000000000 : ℝ)^4255 := by
    have hnat : (2627495863 : ℕ)^5279*6250000000000^4255 ≤ 2813231459153^4255*5000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627495863 5000000000 2813231459153 6250000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (546877759/1000000000 : ℝ)^5279 ≤ (47294587613627/100000000000000 : ℝ)^4255 := by
    have hnat : (546877759 : ℕ)^5279*100000000000000^4255 ≤ 47294587613627^4255*1000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546877759 1000000000 47294587613627 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1265315519/10000000000 : ℝ)^5279 ≤ (7693709028173/100000000000000 : ℝ)^4255 := by
    have hnat : (1265315519 : ℕ)^5279*100000000000000^4255 ≤ 7693709028173^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1265315519 10000000000 7693709028173 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2627495863/5000000000 : ℝ), (546877759/1000000000 : ℝ), (-1265315519/10000000000 : ℝ)] ![(2813231459153/6250000000000 : ℝ), (47294587613627/100000000000000 : ℝ), (7693709028173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2627495863/5000000000 : ℝ)|^5279 ≤ (2813231459153/6250000000000 : ℝ)^4255
        have hw : |(2627495863/5000000000 : ℝ)|=(2627495863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(546877759/1000000000 : ℝ)|^5279 ≤ (47294587613627/100000000000000 : ℝ)^4255
        have hw : |(546877759/1000000000 : ℝ)|=(546877759/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1265315519/10000000000 : ℝ)|^5279 ≤ (7693709028173/100000000000000 : ℝ)^4255
        have hw : |(-1265315519/10000000000 : ℝ)|=(1265315519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_s2_7 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4108912251/10000000000 : ℝ)*x 0 + (919663373/2000000000 : ℝ)*x 1 + (3654907211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4108912251/10000000000 : ℝ)^5279 ≤ (8292913520913/25000000000000 : ℝ)^4255 := by
    have hnat : (4108912251 : ℕ)^5279*25000000000000^4255 ≤ 8292913520913^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4108912251 10000000000 8292913520913 25000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (919663373/2000000000 : ℝ)^5279 ≤ (38141748914179/100000000000000 : ℝ)^4255 := by
    have hnat : (919663373 : ℕ)^5279*100000000000000^4255 ≤ 38141748914179^4255*2000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      919663373 2000000000 38141748914179 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3654907211/10000000000 : ℝ)^5279 ≤ (28686596993907/100000000000000 : ℝ)^4255 := by
    have hnat : (3654907211 : ℕ)^5279*100000000000000^4255 ≤ 28686596993907^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3654907211 10000000000 28686596993907 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4108912251/10000000000 : ℝ), (919663373/2000000000 : ℝ), (3654907211/10000000000 : ℝ)] ![(8292913520913/25000000000000 : ℝ), (38141748914179/100000000000000 : ℝ), (28686596993907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4108912251/10000000000 : ℝ)|^5279 ≤ (8292913520913/25000000000000 : ℝ)^4255
        have hw : |(4108912251/10000000000 : ℝ)|=(4108912251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(919663373/2000000000 : ℝ)|^5279 ≤ (38141748914179/100000000000000 : ℝ)^4255
        have hw : |(919663373/2000000000 : ℝ)|=(919663373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3654907211/10000000000 : ℝ)|^5279 ≤ (28686596993907/100000000000000 : ℝ)^4255
        have hw : |(3654907211/10000000000 : ℝ)|=(3654907211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1707_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24246241/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8723/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4849/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (399/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17127/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8723/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4849/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8723/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4849/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8723/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4849/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8723/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4849/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8723/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4849/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8723/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4849/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4849/50000 : ℝ) ^ (5271/1024 : ℝ) ≤ (608115542062263/100000000000000000000 : ℝ) := by
    have hpowers : (4849/50000 : ℝ)^5271 ≤ (608115542062263/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4849 : ℕ)^5271*100000000000000000000^1024 ≤ 608115542062263^1024*50000^5271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4849 50000 608115542062263 100000000000000000000 5271 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4849/50000 : ℝ)) (X := (608115542062263/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5271 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8723/50000 : ℝ) ^ (5271/1024 : ℝ) ≤ (12492780300960071/100000000000000000000 : ℝ) := by
    have hpowers : (8723/50000 : ℝ)^5271 ≤ (12492780300960071/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8723 : ℕ)^5271*100000000000000000000^1024 ≤ 12492780300960071^1024*50000^5271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8723 50000 12492780300960071 100000000000000000000 5271 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8723/50000 : ℝ)) (X := (12492780300960071/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5271 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000608115542062263/50000000000000000000 : ℝ) ≤ (10000023627670801/10000000000000000 : ℝ) ^ (5271/1024 : ℝ) := by
    have hpowers : (50000608115542062263/50000000000000000000 : ℝ)^1024 ≤ (10000023627670801/10000000000000000 : ℝ)^5271 := by
      have hnat : (50000608115542062263 : ℕ)^1024*10000000000000000^5271 ≤ 10000023627670801^5271*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000608115542062263 50000000000000000000 10000023627670801 10000000000000000 1024 5271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000023627670801/10000000000000000 : ℝ)) (X := (50000608115542062263/50000000000000000000 : ℝ)) (by norm_num) 5271 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50006550447921511167/50000000000000000000 : ℝ) ≤ (10000254498375139/10000000000000000 : ℝ) ^ (5271/1024 : ℝ) := by
    have hpowers : (50006550447921511167/50000000000000000000 : ℝ)^1024 ≤ (10000254498375139/10000000000000000 : ℝ)^5271 := by
      have hnat : (50006550447921511167 : ℕ)^1024*10000000000000000^5271 ≤ 10000254498375139^5271*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006550447921511167 50000000000000000000 10000254498375139 10000000000000000 1024 5271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000254498375139/10000000000000000 : ℝ)) (X := (50006550447921511167/50000000000000000000 : ℝ)) (by norm_num) 5271 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50012492780300960071/50000000000000000000 : ℝ) ≤ (10000485369079477/10000000000000000 : ℝ) ^ (5271/1024 : ℝ) := by
    have hpowers : (50012492780300960071/50000000000000000000 : ℝ)^1024 ≤ (10000485369079477/10000000000000000 : ℝ)^5271 := by
      have hnat : (50012492780300960071 : ℕ)^1024*10000000000000000^5271 ≤ 10000485369079477^5271*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012492780300960071 50000000000000000000 10000485369079477 10000000000000000 1024 5271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000485369079477/10000000000000000 : ℝ)) (X := (50012492780300960071/50000000000000000000 : ℝ)) (by norm_num) 5271 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(608115542062263/100000000000000000000 : ℝ) ≤ ((59596696230009251/59600000000000000 : ℝ)+2*(115435352169/387400000000000 : ℝ)*(4849/50000 : ℝ))^(5271/1024 : ℝ) := by
    rw [show (59596696230009251/59600000000000000 : ℝ)+2*(115435352169/387400000000000 : ℝ)*(4849/50000 : ℝ)=(10000023627670801/10000000000000000 : ℝ) by norm_num, show 1+2*(608115542062263/100000000000000000000 : ℝ)=(50000608115542062263/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12492780300960071/100000000000000000000 : ℝ)+(608115542062263/100000000000000000000 : ℝ) ≤ ((59596696230009251/59600000000000000 : ℝ)+(115435352169/387400000000000 : ℝ)*((8723/50000 : ℝ)+(4849/50000 : ℝ)))^(5271/1024 : ℝ) := by
    rw [show (59596696230009251/59600000000000000 : ℝ)+(115435352169/387400000000000 : ℝ)*((8723/50000 : ℝ)+(4849/50000 : ℝ))=(10000254498375139/10000000000000000 : ℝ) by norm_num, show 1+(12492780300960071/100000000000000000000 : ℝ)+(608115542062263/100000000000000000000 : ℝ)=(50006550447921511167/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12492780300960071/100000000000000000000 : ℝ) ≤ ((59596696230009251/59600000000000000 : ℝ)+2*(115435352169/387400000000000 : ℝ)*(8723/50000 : ℝ))^(5271/1024 : ℝ) := by
    rw [show (59596696230009251/59600000000000000 : ℝ)+2*(115435352169/387400000000000 : ℝ)*(8723/50000 : ℝ)=(10000485369079477/10000000000000000 : ℝ) by norm_num, show 1+2*(12492780300960071/100000000000000000000 : ℝ)=(50012492780300960071/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (59596696230009251/59600000000000000 : ℝ)*(X 1 0+X 2 0)+(115435352169/387400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5271/1024 : ℝ)) (lo := (4849/50000 : ℝ)) (hi := (8723/50000 : ℝ)) (c := (59596696230009251/59600000000000000 : ℝ)) (alpha := (115435352169/387400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (59596696230009251/59600000000000000 : ℝ)*(X 0 1+X 2 1)+(115435352169/387400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5271/1024 : ℝ)) (lo := (4849/50000 : ℝ)) (hi := (8723/50000 : ℝ)) (c := (59596696230009251/59600000000000000 : ℝ)) (alpha := (115435352169/387400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (59596696230009251/59600000000000000 : ℝ)*(X 0 2+X 1 2)+(115435352169/387400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5271/1024 : ℝ)) (lo := (4849/50000 : ℝ)) (hi := (8723/50000 : ℝ)) (c := (59596696230009251/59600000000000000 : ℝ)) (alpha := (115435352169/387400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-711417729/5000000000 : ℝ)*X 0 0+(2736273307/5000000000 : ℝ)*X 0 1+(5137422871/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344689009/10000000000 : ℝ)*X 1 0+(-319334071/2000000000 : ℝ)*X 1 1+(2568711377/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344689013/10000000000 : ℝ)*X 2 0+(5137422803/10000000000 : ℝ)*X 2 1+(-319334057/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4108470187/10000000000 : ℝ)*X 0 0+(227753413/625000000 : ℝ)*X 0 1+(576126201/1250000000 : ℝ)*X 0 2+(4108470187/10000000000 : ℝ)*X 1 0+(227753413/625000000 : ℝ)*X 1 1+(576126201/1250000000 : ℝ)*X 1 2+(4108470187/10000000000 : ℝ)*X 2 0+(227753413/625000000 : ℝ)*X 2 1+(576126201/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-711494503/5000000000 : ℝ)*X 0 0+(2570568121/5000000000 : ℝ)*X 0 1+(5468777623/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((328436987/625000000 : ℝ)*X 1 0+(-316328859/2500000000 : ℝ)*X 1 1+(5468777583/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2627495863/5000000000 : ℝ)*X 2 0+(546877759/1000000000 : ℝ)*X 2 1+(-1265315519/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4108912251/10000000000 : ℝ)*X 0 0+(919663373/2000000000 : ℝ)*X 0 1+(3654907211/10000000000 : ℝ)*X 0 2+(4108912251/10000000000 : ℝ)*X 1 0+(919663373/2000000000 : ℝ)*X 1 1+(3654907211/10000000000 : ℝ)*X 1 2+(4108912251/10000000000 : ℝ)*X 2 0+(919663373/2000000000 : ℝ)*X 2 1+(3654907211/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3136639240127732651360607/298000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1442742913/100000000000000 : ℝ)*(base19) + (1313424483/100000000000000 : ℝ)*(base23) + (35155139/50000000000000 : ℝ)*(lower2) + (227813649/100000000000000 : ℝ)*(upper3) + (4447621/2500000000000 : ℝ)*(upper5) + (201016308610627/10000000000000 : ℝ)*(major0) + (201016308610627/10000000000000 : ℝ)*(major1) + (201016308610627/10000000000000 : ℝ)*(major2) + (372998174696197/12500000000000 : ℝ)*(sp0) + (29839971979883/1000000000000 : ℝ)*(sp1) + (2983997327306731/100000000000000 : ℝ)*(sp2) + (518161076100329/50000000000000 : ℝ)*(sp3) + (6621580819/50000000000000 : ℝ)*(sp4) + (62855327/1250000000000 : ℝ)*(sp7) + (1036327180626819/100000000000000 : ℝ)*(f.failure) + (1491999320365607/50000000000000 : ℝ)*(f.sum) + (1535275071127/1937000000000000000000000000 : ℝ)*base66 + (20200513549808901/7748000000000000000000000000000 : ℝ)*base67 + (10780956388248901/7748000000000000000000000000000 : ℝ)*base69 + (47671486226072901/7748000000000000000000000000000 : ℝ)*base71 + (390726593661/387400000000000000000000000 : ℝ)*base74 + (133019765263808901/7748000000000000000000000000000 : ℝ)*base75 + (129356856428901/7748000000000000000000000000000 : ℝ)*base77 + (7333511192924901/7748000000000000000000000000000 : ℝ)*base79 + (185465134823/193700000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (9537379/1250000000000000000000 : ℝ)*base89 + (9537379/1250000000000000000000 : ℝ)*base91 + (9537379/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (103793745554489716557926397/9685000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (91463783/6250000000000 : ℝ)*(base19) + (1545689579/100000000000000 : ℝ)*(base23) + (206836527/100000000000000 : ℝ)*(upper3) + (65108993/100000000000000 : ℝ)*(lower4) + (122181701/50000000000000 : ℝ)*(upper5) + (514012756435091/25000000000000 : ℝ)*(major0) + (514012756435091/25000000000000 : ℝ)*(major1) + (514012756435091/25000000000000 : ℝ)*(major2) + (6700723149/50000000000000 : ℝ)*(sp1) + (13208262747/100000000000000 : ℝ)*(sp2) + (152605863468711/5000000000000 : ℝ)*(sp4) + (1526051202253697/50000000000000 : ℝ)*(sp5) + (1526051257710947/50000000000000 : ℝ)*(sp6) + (1059984424874543/100000000000000 : ℝ)*(sp7) + (1059984424874543/100000000000000 : ℝ)*(f.failure) + (152605863468711/5000000000000 : ℝ)*(f.sum) + (17385073201253/9685000000000000000000000000 : ℝ)*base65 + (198826272502843067/19370000000000000000000000000000 : ℝ)*base68 + (240044851853103067/19370000000000000000000000000000 : ℝ)*base70 + (26123857827403067/19370000000000000000000000000000 : ℝ)*base72 + (16800431077127/9685000000000000000000000000 : ℝ)*base74 + (138742353902683067/19370000000000000000000000000000 : ℝ)*base76 + (68344627941653067/19370000000000000000000000000000 : ℝ)*base78 + (172740578464413067/19370000000000000000000000000000 : ℝ)*base80 + (28847408216131/4842500000000000000000000000 : ℝ)*base82 + (14342863/1250000000000000000000 : ℝ)*base89 + (14342863/1250000000000000000000 : ℝ)*base91 + (14342863/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1707_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24246241/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8723/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4849/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (399/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17127/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1707_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1707_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24246241/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (399/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17127/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1707_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1707_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1707_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24246241/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (399/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17127/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1707_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

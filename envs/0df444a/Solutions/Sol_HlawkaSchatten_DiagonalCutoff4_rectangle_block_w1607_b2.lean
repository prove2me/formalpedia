-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1607_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:50:56.64465+00:00
-- url     : https://prove2.me/submissions/dd9a60a6-dcf2-4165-a72a-762641f62f9d

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
theorem support_rectangle_w1607_box_0 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-359339837/2500000000 : ℝ)*x 0 + (2709432287/5000000000 : ℝ)*x 1 + (5418864741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (359339837/2500000000 : ℝ)^4747 ≤ (8430556289683/100000000000000 : ℝ)^3723 := by
    have hnat : (359339837 : ℕ)^4747*100000000000000^3723 ≤ 8430556289683^3723*2500000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      359339837 2500000000 8430556289683 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2709432287/5000000000 : ℝ)^4747 ≤ (9156944189779/20000000000000 : ℝ)^3723 := by
    have hnat : (2709432287 : ℕ)^4747*20000000000000^3723 ≤ 9156944189779^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709432287 5000000000 9156944189779 20000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5418864741/10000000000 : ℝ)^4747 ≤ (45784722747993/100000000000000 : ℝ)^3723 := by
    have hnat : (5418864741 : ℕ)^4747*100000000000000^3723 ≤ 45784722747993^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418864741 10000000000 45784722747993 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-359339837/2500000000 : ℝ), (2709432287/5000000000 : ℝ), (5418864741/10000000000 : ℝ)] ![(8430556289683/100000000000000 : ℝ), (9156944189779/20000000000000 : ℝ), (45784722747993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-359339837/2500000000 : ℝ)|^4747 ≤ (8430556289683/100000000000000 : ℝ)^3723
        have hw : |(-359339837/2500000000 : ℝ)|=(359339837/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2709432287/5000000000 : ℝ)|^4747 ≤ (9156944189779/20000000000000 : ℝ)^3723
        have hw : |(2709432287/5000000000 : ℝ)|=(2709432287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5418864741/10000000000 : ℝ)|^4747 ≤ (45784722747993/100000000000000 : ℝ)^3723
        have hw : |(5418864741/10000000000 : ℝ)|=(5418864741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_box_1 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (328195081/625000000 : ℝ)*x 0 + (-1672851/10000000 : ℝ)*x 1 + (338679093/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328195081/625000000 : ℝ)^4747 ≤ (8797073288307/20000000000000 : ℝ)^3723 := by
    have hnat : (328195081 : ℕ)^4747*20000000000000^3723 ≤ 8797073288307^3723*625000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328195081 625000000 8797073288307 20000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1672851/10000000 : ℝ)^4747 ≤ (10229902756279/100000000000000 : ℝ)^3723 := by
    have hnat : (1672851 : ℕ)^4747*100000000000000^3723 ≤ 10229902756279^3723*10000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1672851 10000000 10229902756279 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338679093/625000000 : ℝ)^4747 ≤ (22892365397729/50000000000000 : ℝ)^3723 := by
    have hnat : (338679093 : ℕ)^4747*50000000000000^3723 ≤ 22892365397729^3723*625000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338679093 625000000 22892365397729 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328195081/625000000 : ℝ), (-1672851/10000000 : ℝ), (338679093/625000000 : ℝ)] ![(8797073288307/20000000000000 : ℝ), (10229902756279/100000000000000 : ℝ), (22892365397729/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328195081/625000000 : ℝ)|^4747 ≤ (8797073288307/20000000000000 : ℝ)^3723
        have hw : |(328195081/625000000 : ℝ)|=(328195081/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1672851/10000000 : ℝ)|^4747 ≤ (10229902756279/100000000000000 : ℝ)^3723
        have hw : |(-1672851/10000000 : ℝ)|=(1672851/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338679093/625000000 : ℝ)|^4747 ≤ (22892365397729/50000000000000 : ℝ)^3723
        have hw : |(338679093/625000000 : ℝ)|=(338679093/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_box_2 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625560541/5000000000 : ℝ)*x 0 + (5418865563/10000000000 : ℝ)*x 1 + (-418212797/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625560541/5000000000 : ℝ)^4747 ≤ (43985364155957/100000000000000 : ℝ)^3723 := by
    have hnat : (2625560541 : ℕ)^4747*100000000000000^3723 ≤ 43985364155957^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625560541 5000000000 43985364155957 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5418865563/10000000000 : ℝ)^4747 ≤ (45784731603437/100000000000000 : ℝ)^3723 := by
    have hnat : (5418865563 : ℕ)^4747*100000000000000^3723 ≤ 45784731603437^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418865563 10000000000 45784731603437 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (418212797/2500000000 : ℝ)^4747 ≤ (5114952111079/50000000000000 : ℝ)^3723 := by
    have hnat : (418212797 : ℕ)^4747*50000000000000^3723 ≤ 5114952111079^3723*2500000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418212797 2500000000 5114952111079 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625560541/5000000000 : ℝ), (5418865563/10000000000 : ℝ), (-418212797/2500000000 : ℝ)] ![(43985364155957/100000000000000 : ℝ), (45784731603437/100000000000000 : ℝ), (5114952111079/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625560541/5000000000 : ℝ)|^4747 ≤ (43985364155957/100000000000000 : ℝ)^3723
        have hw : |(2625560541/5000000000 : ℝ)|=(2625560541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5418865563/10000000000 : ℝ)|^4747 ≤ (45784731603437/100000000000000 : ℝ)^3723
        have hw : |(5418865563/10000000000 : ℝ)|=(5418865563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-418212797/2500000000 : ℝ)|^4747 ≤ (5114952111079/50000000000000 : ℝ)^3723
        have hw : |(-418212797/2500000000 : ℝ)|=(418212797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_box_3 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (449515001/1000000000 : ℝ)*x 0 + (510970299/1250000000 : ℝ)*x 1 + (4087762879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (449515001/1000000000 : ℝ)^4747 ≤ (18038587317749/50000000000000 : ℝ)^3723 := by
    have hnat : (449515001 : ℕ)^4747*50000000000000^3723 ≤ 18038587317749^3723*1000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449515001 1000000000 18038587317749 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (510970299/1250000000 : ℝ)^4747 ≤ (31961410248687/100000000000000 : ℝ)^3723 := by
    have hnat : (510970299 : ℕ)^4747*100000000000000^3723 ≤ 31961410248687^3723*1250000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510970299 1250000000 31961410248687 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4087762879/10000000000 : ℝ)^4747 ≤ (31961415103757/100000000000000 : ℝ)^3723 := by
    have hnat : (4087762879 : ℕ)^4747*100000000000000^3723 ≤ 31961415103757^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4087762879 10000000000 31961415103757 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(449515001/1000000000 : ℝ), (510970299/1250000000 : ℝ), (4087762879/10000000000 : ℝ)] ![(18038587317749/50000000000000 : ℝ), (31961410248687/100000000000000 : ℝ), (31961415103757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(449515001/1000000000 : ℝ)|^4747 ≤ (18038587317749/50000000000000 : ℝ)^3723
        have hw : |(449515001/1000000000 : ℝ)|=(449515001/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(510970299/1250000000 : ℝ)|^4747 ≤ (31961410248687/100000000000000 : ℝ)^3723
        have hw : |(510970299/1250000000 : ℝ)|=(510970299/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4087762879/10000000000 : ℝ)|^4747 ≤ (31961415103757/100000000000000 : ℝ)^3723
        have hw : |(4087762879/10000000000 : ℝ)|=(4087762879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_box_4 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-249642383/1250000000 : ℝ)*x 0 + (5213928317/10000000000 : ℝ)*x 1 + (5213929389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (249642383/1250000000 : ℝ)^4747 ≤ (12822942843557/100000000000000 : ℝ)^3723 := by
    have hnat : (249642383 : ℕ)^4747*100000000000000^3723 ≤ 12822942843557^3723*1250000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249642383 1250000000 12822942843557 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5213928317/10000000000 : ℝ)^4747 ≤ (21794261429103/50000000000000 : ℝ)^3723 := by
    have hnat : (5213928317 : ℕ)^4747*50000000000000^3723 ≤ 21794261429103^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5213928317 10000000000 21794261429103 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5213929389/10000000000 : ℝ)^4747 ≤ (43588534285097/100000000000000 : ℝ)^3723 := by
    have hnat : (5213929389 : ℕ)^4747*100000000000000^3723 ≤ 43588534285097^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5213929389 10000000000 43588534285097 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-249642383/1250000000 : ℝ), (5213928317/10000000000 : ℝ), (5213929389/10000000000 : ℝ)] ![(12822942843557/100000000000000 : ℝ), (21794261429103/50000000000000 : ℝ), (43588534285097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-249642383/1250000000 : ℝ)|^4747 ≤ (12822942843557/100000000000000 : ℝ)^3723
        have hw : |(-249642383/1250000000 : ℝ)|=(249642383/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5213928317/10000000000 : ℝ)|^4747 ≤ (21794261429103/50000000000000 : ℝ)^3723
        have hw : |(5213928317/10000000000 : ℝ)|=(5213928317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5213929389/10000000000 : ℝ)|^4747 ≤ (43588534285097/100000000000000 : ℝ)^3723
        have hw : |(5213929389/10000000000 : ℝ)|=(5213929389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_box_5 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5392623213/10000000000 : ℝ)*x 0 + (-1759370427/10000000000 : ℝ)*x 1 + (2606964751/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5392623213/10000000000 : ℝ)^4747 ≤ (45502210078993/100000000000000 : ℝ)^3723 := by
    have hnat : (5392623213 : ℕ)^4747*100000000000000^3723 ≤ 45502210078993^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392623213 10000000000 45502210078993 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1759370427/10000000000 : ℝ)^4747 ≤ (10909254407443/100000000000000 : ℝ)^3723 := by
    have hnat : (1759370427 : ℕ)^4747*100000000000000^3723 ≤ 10909254407443^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1759370427 10000000000 10909254407443 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2606964751/5000000000 : ℝ)^4747 ≤ (4358853548961/10000000000000 : ℝ)^3723 := by
    have hnat : (2606964751 : ℕ)^4747*10000000000000^3723 ≤ 4358853548961^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2606964751 5000000000 4358853548961 10000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5392623213/10000000000 : ℝ), (-1759370427/10000000000 : ℝ), (2606964751/5000000000 : ℝ)] ![(45502210078993/100000000000000 : ℝ), (10909254407443/100000000000000 : ℝ), (4358853548961/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5392623213/10000000000 : ℝ)|^4747 ≤ (45502210078993/100000000000000 : ℝ)^3723
        have hw : |(5392623213/10000000000 : ℝ)|=(5392623213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1759370427/10000000000 : ℝ)|^4747 ≤ (10909254407443/100000000000000 : ℝ)^3723
        have hw : |(-1759370427/10000000000 : ℝ)|=(1759370427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2606964751/5000000000 : ℝ)|^4747 ≤ (4358853548961/10000000000000 : ℝ)^3723
        have hw : |(2606964751/5000000000 : ℝ)|=(2606964751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_box_6 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (674077953/1250000000 : ℝ)*x 0 + (5213928379/10000000000 : ℝ)*x 1 + (-219921423/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (674077953/1250000000 : ℝ)^4747 ≤ (45502214500807/100000000000000 : ℝ)^3723 := by
    have hnat : (674077953 : ℕ)^4747*100000000000000^3723 ≤ 45502214500807^3723*1250000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674077953 1250000000 45502214500807 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5213928379/10000000000 : ℝ)^4747 ≤ (43588523519089/100000000000000 : ℝ)^3723 := by
    have hnat : (5213928379 : ℕ)^4747*100000000000000^3723 ≤ 43588523519089^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5213928379 10000000000 43588523519089 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219921423/1250000000 : ℝ)^4747 ≤ (1090926197361/10000000000000 : ℝ)^3723 := by
    have hnat : (219921423 : ℕ)^4747*10000000000000^3723 ≤ 1090926197361^3723*1250000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219921423 1250000000 1090926197361 10000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(674077953/1250000000 : ℝ), (5213928379/10000000000 : ℝ), (-219921423/1250000000 : ℝ)] ![(45502214500807/100000000000000 : ℝ), (43588523519089/100000000000000 : ℝ), (1090926197361/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(674077953/1250000000 : ℝ)|^4747 ≤ (45502214500807/100000000000000 : ℝ)^3723
        have hw : |(674077953/1250000000 : ℝ)|=(674077953/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5213928379/10000000000 : ℝ)|^4747 ≤ (43588523519089/100000000000000 : ℝ)^3723
        have hw : |(5213928379/10000000000 : ℝ)|=(5213928379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-219921423/1250000000 : ℝ)|^4747 ≤ (1090926197361/10000000000000 : ℝ)^3723
        have hw : |(-219921423/1250000000 : ℝ)|=(219921423/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_box_7 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3929090401/10000000000 : ℝ)*x 0 + (2185223693/5000000000 : ℝ)*x 1 + (546305919/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3929090401/10000000000 : ℝ)^4747 ≤ (15194039848097/50000000000000 : ℝ)^3723 := by
    have hnat : (3929090401 : ℕ)^4747*50000000000000^3723 ≤ 15194039848097^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3929090401 10000000000 15194039848097 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2185223693/5000000000 : ℝ)^4747 ≤ (17402980157619/50000000000000 : ℝ)^3723 := by
    have hnat : (2185223693 : ℕ)^4747*50000000000000^3723 ≤ 17402980157619^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185223693 5000000000 17402980157619 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (546305919/1250000000 : ℝ)^4747 ≤ (8701489992497/25000000000000 : ℝ)^3723 := by
    have hnat : (546305919 : ℕ)^4747*25000000000000^3723 ≤ 8701489992497^3723*1250000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546305919 1250000000 8701489992497 25000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3929090401/10000000000 : ℝ), (2185223693/5000000000 : ℝ), (546305919/1250000000 : ℝ)] ![(15194039848097/50000000000000 : ℝ), (17402980157619/50000000000000 : ℝ), (8701489992497/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3929090401/10000000000 : ℝ)|^4747 ≤ (15194039848097/50000000000000 : ℝ)^3723
        have hw : |(3929090401/10000000000 : ℝ)|=(3929090401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2185223693/5000000000 : ℝ)|^4747 ≤ (17402980157619/50000000000000 : ℝ)^3723
        have hw : |(2185223693/5000000000 : ℝ)|=(2185223693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(546305919/1250000000 : ℝ)|^4747 ≤ (8701489992497/25000000000000 : ℝ)^3723
        have hw : |(546305919/1250000000 : ℝ)|=(546305919/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_box_8 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1878158851/10000000000 : ℝ)*x 0 + (1013524677/2000000000 : ℝ)*x 1 + (1089769043/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1878158851/10000000000 : ℝ)^4747 ≤ (11856993214251/100000000000000 : ℝ)^3723 := by
    have hnat : (1878158851 : ℕ)^4747*100000000000000^3723 ≤ 11856993214251^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1878158851 10000000000 11856993214251 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1013524677/2000000000 : ℝ)^4747 ≤ (42035057617933/100000000000000 : ℝ)^3723 := by
    have hnat : (1013524677 : ℕ)^4747*100000000000000^3723 ≤ 42035057617933^3723*2000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013524677 2000000000 42035057617933 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1089769043/2000000000 : ℝ)^4747 ≤ (46107949159933/100000000000000 : ℝ)^3723 := by
    have hnat : (1089769043 : ℕ)^4747*100000000000000^3723 ≤ 46107949159933^3723*2000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089769043 2000000000 46107949159933 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1878158851/10000000000 : ℝ), (1013524677/2000000000 : ℝ), (1089769043/2000000000 : ℝ)] ![(11856993214251/100000000000000 : ℝ), (42035057617933/100000000000000 : ℝ), (46107949159933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1878158851/10000000000 : ℝ)|^4747 ≤ (11856993214251/100000000000000 : ℝ)^3723
        have hw : |(-1878158851/10000000000 : ℝ)|=(1878158851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1013524677/2000000000 : ℝ)|^4747 ≤ (42035057617933/100000000000000 : ℝ)^3723
        have hw : |(1013524677/2000000000 : ℝ)|=(1013524677/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1089769043/2000000000 : ℝ)|^4747 ≤ (46107949159933/100000000000000 : ℝ)^3723
        have hw : |(1089769043/2000000000 : ℝ)|=(1089769043/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_box_9 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1046083129/2000000000 : ℝ)*x 0 + (-41493233/250000000 : ℝ)*x 1 + (5448845753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1046083129/2000000000 : ℝ)^4747 ≤ (43764344465881/100000000000000 : ℝ)^3723 := by
    have hnat : (1046083129 : ℕ)^4747*100000000000000^3723 ≤ 43764344465881^3723*2000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046083129 2000000000 43764344465881 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41493233/250000000 : ℝ)^4747 ≤ (5063850276837/50000000000000 : ℝ)^3723 := by
    have hnat : (41493233 : ℕ)^4747*50000000000000^3723 ≤ 5063850276837^3723*250000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41493233 250000000 5063850276837 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5448845753/10000000000 : ℝ)^4747 ≤ (23053977482317/50000000000000 : ℝ)^3723 := by
    have hnat : (5448845753 : ℕ)^4747*50000000000000^3723 ≤ 23053977482317^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5448845753 10000000000 23053977482317 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1046083129/2000000000 : ℝ), (-41493233/250000000 : ℝ), (5448845753/10000000000 : ℝ)] ![(43764344465881/100000000000000 : ℝ), (5063850276837/50000000000000 : ℝ), (23053977482317/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1046083129/2000000000 : ℝ)|^4747 ≤ (43764344465881/100000000000000 : ℝ)^3723
        have hw : |(1046083129/2000000000 : ℝ)|=(1046083129/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-41493233/250000000 : ℝ)|^4747 ≤ (5063850276837/50000000000000 : ℝ)^3723
        have hw : |(-41493233/250000000 : ℝ)|=(41493233/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5448845753/10000000000 : ℝ)|^4747 ≤ (23053977482317/50000000000000 : ℝ)^3723
        have hw : |(5448845753/10000000000 : ℝ)|=(5448845753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_box_10 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230416257/10000000000 : ℝ)*x 0 + (1362211531/2500000000 : ℝ)*x 1 + (-829863983/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230416257/10000000000 : ℝ)^4747 ≤ (43764350995109/100000000000000 : ℝ)^3723 := by
    have hnat : (5230416257 : ℕ)^4747*100000000000000^3723 ≤ 43764350995109^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230416257 10000000000 43764350995109 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1362211531/2500000000 : ℝ)^4747 ≤ (46107958967503/100000000000000 : ℝ)^3723 := by
    have hnat : (1362211531 : ℕ)^4747*100000000000000^3723 ≤ 46107958967503^3723*2500000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362211531 2500000000 46107958967503 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (829863983/5000000000 : ℝ)^4747 ≤ (2025538003813/20000000000000 : ℝ)^3723 := by
    have hnat : (829863983 : ℕ)^4747*20000000000000^3723 ≤ 2025538003813^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      829863983 5000000000 2025538003813 20000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230416257/10000000000 : ℝ), (1362211531/2500000000 : ℝ), (-829863983/5000000000 : ℝ)] ![(43764350995109/100000000000000 : ℝ), (46107958967503/100000000000000 : ℝ), (2025538003813/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230416257/10000000000 : ℝ)|^4747 ≤ (43764350995109/100000000000000 : ℝ)^3723
        have hw : |(5230416257/10000000000 : ℝ)|=(5230416257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1362211531/2500000000 : ℝ)|^4747 ≤ (46107958967503/100000000000000 : ℝ)^3723
        have hw : |(1362211531/2500000000 : ℝ)|=(1362211531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-829863983/5000000000 : ℝ)|^4747 ≤ (2025538003813/20000000000000 : ℝ)^3723
        have hw : |(-829863983/5000000000 : ℝ)|=(829863983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_box_11 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (142986383/312500000 : ℝ)*x 0 + (2023166451/5000000000 : ℝ)*x 1 + (2023165621/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (142986383/312500000 : ℝ)^4747 ≤ (9225522823693/25000000000000 : ℝ)^3723 := by
    have hnat : (142986383 : ℕ)^4747*25000000000000^3723 ≤ 9225522823693^3723*312500000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142986383 312500000 9225522823693 25000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2023166451/5000000000 : ℝ)^4747 ≤ (7887240648371/25000000000000 : ℝ)^3723 := by
    have hnat : (2023166451 : ℕ)^4747*25000000000000^3723 ≤ 7887240648371^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2023166451 5000000000 7887240648371 25000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2023165621/5000000000 : ℝ)^4747 ≤ (788723652267/2500000000000 : ℝ)^3723 := by
    have hnat : (2023165621 : ℕ)^4747*2500000000000^3723 ≤ 788723652267^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2023165621 5000000000 788723652267 2500000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(142986383/312500000 : ℝ), (2023166451/5000000000 : ℝ), (2023165621/5000000000 : ℝ)] ![(9225522823693/25000000000000 : ℝ), (7887240648371/25000000000000 : ℝ), (788723652267/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(142986383/312500000 : ℝ)|^4747 ≤ (9225522823693/25000000000000 : ℝ)^3723
        have hw : |(142986383/312500000 : ℝ)|=(142986383/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2023166451/5000000000 : ℝ)|^4747 ≤ (7887240648371/25000000000000 : ℝ)^3723
        have hw : |(2023166451/5000000000 : ℝ)|=(2023166451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2023165621/5000000000 : ℝ)|^4747 ≤ (788723652267/2500000000000 : ℝ)^3723
        have hw : |(2023165621/5000000000 : ℝ)|=(2023165621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_box_12 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-311032693/2000000000 : ℝ)*x 0 + (1111839413/2000000000 : ℝ)*x 1 + (5194057273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (311032693/2000000000 : ℝ)^4747 ≤ (2330324897907/25000000000000 : ℝ)^3723 := by
    have hnat : (311032693 : ℕ)^4747*25000000000000^3723 ≤ 2330324897907^3723*2000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      311032693 2000000000 2330324897907 25000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1111839413/2000000000 : ℝ)^4747 ≤ (47301880080259/100000000000000 : ℝ)^3723 := by
    have hnat : (1111839413 : ℕ)^4747*100000000000000^3723 ≤ 47301880080259^3723*2000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1111839413 2000000000 47301880080259 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5194057273/10000000000 : ℝ)^4747 ≤ (43376820311193/100000000000000 : ℝ)^3723 := by
    have hnat : (5194057273 : ℕ)^4747*100000000000000^3723 ≤ 43376820311193^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194057273 10000000000 43376820311193 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-311032693/2000000000 : ℝ), (1111839413/2000000000 : ℝ), (5194057273/10000000000 : ℝ)] ![(2330324897907/25000000000000 : ℝ), (47301880080259/100000000000000 : ℝ), (43376820311193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-311032693/2000000000 : ℝ)|^4747 ≤ (2330324897907/25000000000000 : ℝ)^3723
        have hw : |(-311032693/2000000000 : ℝ)|=(311032693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1111839413/2000000000 : ℝ)|^4747 ≤ (47301880080259/100000000000000 : ℝ)^3723
        have hw : |(1111839413/2000000000 : ℝ)|=(1111839413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5194057273/10000000000 : ℝ)|^4747 ≤ (43376820311193/100000000000000 : ℝ)^3723
        have hw : |(5194057273/10000000000 : ℝ)|=(5194057273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_box_13 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1351587483/2500000000 : ℝ)*x 0 + (-1767456701/10000000000 : ℝ)*x 1 + (1038811657/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1351587483/2500000000 : ℝ)^4747 ≤ (22824971496231/50000000000000 : ℝ)^3723 := by
    have hnat : (1351587483 : ℕ)^4747*50000000000000^3723 ≤ 22824971496231^3723*2500000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351587483 2500000000 22824971496231 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1767456701/10000000000 : ℝ)^4747 ≤ (1371653238653/12500000000000 : ℝ)^3723 := by
    have hnat : (1767456701 : ℕ)^4747*12500000000000^3723 ≤ 1371653238653^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1767456701 10000000000 1371653238653 12500000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1038811657/2000000000 : ℝ)^4747 ≤ (10844207771799/25000000000000 : ℝ)^3723 := by
    have hnat : (1038811657 : ℕ)^4747*25000000000000^3723 ≤ 10844207771799^3723*2000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038811657 2000000000 10844207771799 25000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1351587483/2500000000 : ℝ), (-1767456701/10000000000 : ℝ), (1038811657/2000000000 : ℝ)] ![(22824971496231/50000000000000 : ℝ), (1371653238653/12500000000000 : ℝ), (10844207771799/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1351587483/2500000000 : ℝ)|^4747 ≤ (22824971496231/50000000000000 : ℝ)^3723
        have hw : |(1351587483/2500000000 : ℝ)|=(1351587483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1767456701/10000000000 : ℝ)|^4747 ≤ (1371653238653/12500000000000 : ℝ)^3723
        have hw : |(-1767456701/10000000000 : ℝ)|=(1767456701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1038811657/2000000000 : ℝ)|^4747 ≤ (10844207771799/25000000000000 : ℝ)^3723
        have hw : |(1038811657/2000000000 : ℝ)|=(1038811657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_box_14 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (270317569/500000000 : ℝ)*x 0 + (5194057337/10000000000 : ℝ)*x 1 + (-883728003/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270317569/500000000 : ℝ)^4747 ≤ (22824979290957/50000000000000 : ℝ)^3723 := by
    have hnat : (270317569 : ℕ)^4747*50000000000000^3723 ≤ 22824979290957^3723*500000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270317569 500000000 22824979290957 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5194057337/10000000000 : ℝ)^4747 ≤ (1084420524817/2500000000000 : ℝ)^3723 := by
    have hnat : (5194057337 : ℕ)^4747*2500000000000^3723 ≤ 1084420524817^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194057337 10000000000 1084420524817 2500000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (883728003/5000000000 : ℝ)^4747 ≤ (10973220407529/100000000000000 : ℝ)^3723 := by
    have hnat : (883728003 : ℕ)^4747*100000000000000^3723 ≤ 10973220407529^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883728003 5000000000 10973220407529 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(270317569/500000000 : ℝ), (5194057337/10000000000 : ℝ), (-883728003/5000000000 : ℝ)] ![(22824979290957/50000000000000 : ℝ), (1084420524817/2500000000000 : ℝ), (10973220407529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(270317569/500000000 : ℝ)|^4747 ≤ (22824979290957/50000000000000 : ℝ)^3723
        have hw : |(270317569/500000000 : ℝ)|=(270317569/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5194057337/10000000000 : ℝ)|^4747 ≤ (1084420524817/2500000000000 : ℝ)^3723
        have hw : |(5194057337/10000000000 : ℝ)|=(5194057337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-883728003/5000000000 : ℝ)|^4747 ≤ (10973220407529/100000000000000 : ℝ)^3723
        have hw : |(-883728003/5000000000 : ℝ)|=(883728003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_box_15 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1936291183/5000000000 : ℝ)*x 0 + (4397807689/10000000000 : ℝ)*x 1 + (34357879/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1936291183/5000000000 : ℝ)^4747 ≤ (1193277553497/4000000000000 : ℝ)^3723 := by
    have hnat : (1936291183 : ℕ)^4747*4000000000000^3723 ≤ 1193277553497^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1936291183 5000000000 1193277553497 4000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4397807689/10000000000 : ℝ)^4747 ≤ (7016805277021/20000000000000 : ℝ)^3723 := by
    have hnat : (4397807689 : ℕ)^4747*20000000000000^3723 ≤ 7016805277021^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4397807689 10000000000 7016805277021 20000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34357879/78125000 : ℝ)^4747 ≤ (35084034756527/100000000000000 : ℝ)^3723 := by
    have hnat : (34357879 : ℕ)^4747*100000000000000^3723 ≤ 35084034756527^3723*78125000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34357879 78125000 35084034756527 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1936291183/5000000000 : ℝ), (4397807689/10000000000 : ℝ), (34357879/78125000 : ℝ)] ![(1193277553497/4000000000000 : ℝ), (7016805277021/20000000000000 : ℝ), (35084034756527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1936291183/5000000000 : ℝ)|^4747 ≤ (1193277553497/4000000000000 : ℝ)^3723
        have hw : |(1936291183/5000000000 : ℝ)|=(1936291183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4397807689/10000000000 : ℝ)|^4747 ≤ (7016805277021/20000000000000 : ℝ)^3723
        have hw : |(4397807689/10000000000 : ℝ)|=(4397807689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(34357879/78125000 : ℝ)|^4747 ≤ (35084034756527/100000000000000 : ℝ)^3723
        have hw : |(34357879/78125000 : ℝ)|=(34357879/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1607_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2154773/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8173/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (651/6250 : ℝ)*pair X i i ≤ pair X i h) :
    -(6491/10000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29081/50000 : ℝ) ∧ (40187/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (87793/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8173/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (651/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8173/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (651/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8173/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (651/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8173/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (651/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8173/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (651/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8173/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (651/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (651/6250 : ℝ) ^ (4743/1024 : ℝ) ≤ (1409684944494097/50000000000000000000 : ℝ) := by
    have hpowers : (651/6250 : ℝ)^4743 ≤ (1409684944494097/50000000000000000000 : ℝ)^1024 := by
      have hnat : (651 : ℕ)^4743*50000000000000000000^1024 ≤ 1409684944494097^1024*6250^4743 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        651 6250 1409684944494097 50000000000000000000 4743 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (651/6250 : ℝ)) (X := (1409684944494097/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4743 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8173/50000 : ℝ) ^ (4743/1024 : ℝ) ≤ (11366351882524273/50000000000000000000 : ℝ) := by
    have hpowers : (8173/50000 : ℝ)^4743 ≤ (11366351882524273/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8173 : ℕ)^4743*50000000000000000000^1024 ≤ 11366351882524273^1024*50000^4743 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8173 50000 11366351882524273 50000000000000000000 4743 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8173/50000 : ℝ)) (X := (11366351882524273/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4743 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001409684944494097/25000000000000000000 : ℝ) ≤ (2500030434017979/2500000000000000 : ℝ) ^ (4743/1024 : ℝ) := by
    have hpowers : (25001409684944494097/25000000000000000000 : ℝ)^1024 ≤ (2500030434017979/2500000000000000 : ℝ)^4743 := by
      have hnat : (25001409684944494097 : ℕ)^1024*2500000000000000^4743 ≤ 2500030434017979^4743*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001409684944494097 25000000000000000000 2500030434017979 2500000000000000 1024 4743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500030434017979/2500000000000000 : ℝ)) (X := (25001409684944494097/25000000000000000000 : ℝ)) (by norm_num) 4743 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5001277603682701837/5000000000000000000 : ℝ) ≤ (10000551606633971/10000000000000000 : ℝ) ^ (4743/1024 : ℝ) := by
    have hpowers : (5001277603682701837/5000000000000000000 : ℝ)^1024 ≤ (10000551606633971/10000000000000000 : ℝ)^4743 := by
      have hnat : (5001277603682701837 : ℕ)^1024*10000000000000000^4743 ≤ 10000551606633971^4743*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001277603682701837 5000000000000000000 10000551606633971 10000000000000000 1024 4743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000551606633971/10000000000000000 : ℝ)) (X := (5001277603682701837/5000000000000000000 : ℝ)) (by norm_num) 4743 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25011366351882524273/25000000000000000000 : ℝ) ≤ (5000490738598013/5000000000000000 : ℝ) ^ (4743/1024 : ℝ) := by
    have hpowers : (25011366351882524273/25000000000000000000 : ℝ)^1024 ≤ (5000490738598013/5000000000000000 : ℝ)^4743 := by
      have hnat : (25011366351882524273 : ℕ)^1024*5000000000000000^4743 ≤ 5000490738598013^4743*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011366351882524273 25000000000000000000 5000490738598013 5000000000000000 1024 4743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000490738598013/5000000000000000 : ℝ)) (X := (25011366351882524273/25000000000000000000 : ℝ)) (by norm_num) 4743 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1409684944494097/50000000000000000000 : ℝ) ≤ ((1482294170783943303/1482500000000000000 : ℝ)+2*(85974112411/118600000000000 : ℝ)*(651/6250 : ℝ))^(4743/1024 : ℝ) := by
    rw [show (1482294170783943303/1482500000000000000 : ℝ)+2*(85974112411/118600000000000 : ℝ)*(651/6250 : ℝ)=(2500030434017979/2500000000000000 : ℝ) by norm_num, show 1+2*(1409684944494097/50000000000000000000 : ℝ)=(25001409684944494097/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11366351882524273/50000000000000000000 : ℝ)+(1409684944494097/50000000000000000000 : ℝ) ≤ ((1482294170783943303/1482500000000000000 : ℝ)+(85974112411/118600000000000 : ℝ)*((8173/50000 : ℝ)+(651/6250 : ℝ)))^(4743/1024 : ℝ) := by
    rw [show (1482294170783943303/1482500000000000000 : ℝ)+(85974112411/118600000000000 : ℝ)*((8173/50000 : ℝ)+(651/6250 : ℝ))=(10000551606633971/10000000000000000 : ℝ) by norm_num, show 1+(11366351882524273/50000000000000000000 : ℝ)+(1409684944494097/50000000000000000000 : ℝ)=(5001277603682701837/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11366351882524273/50000000000000000000 : ℝ) ≤ ((1482294170783943303/1482500000000000000 : ℝ)+2*(85974112411/118600000000000 : ℝ)*(8173/50000 : ℝ))^(4743/1024 : ℝ) := by
    rw [show (1482294170783943303/1482500000000000000 : ℝ)+2*(85974112411/118600000000000 : ℝ)*(8173/50000 : ℝ)=(5000490738598013/5000000000000000 : ℝ) by norm_num, show 1+2*(11366351882524273/50000000000000000000 : ℝ)=(25011366351882524273/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1482294170783943303/1482500000000000000 : ℝ)*(X 1 0+X 2 0)+(85974112411/118600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4743/1024 : ℝ)) (lo := (651/6250 : ℝ)) (hi := (8173/50000 : ℝ)) (c := (1482294170783943303/1482500000000000000 : ℝ)) (alpha := (85974112411/118600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1482294170783943303/1482500000000000000 : ℝ)*(X 0 1+X 2 1)+(85974112411/118600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4743/1024 : ℝ)) (lo := (651/6250 : ℝ)) (hi := (8173/50000 : ℝ)) (c := (1482294170783943303/1482500000000000000 : ℝ)) (alpha := (85974112411/118600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1482294170783943303/1482500000000000000 : ℝ)*(X 0 2+X 1 2)+(85974112411/118600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4743/1024 : ℝ)) (lo := (651/6250 : ℝ)) (hi := (8173/50000 : ℝ)) (c := (1482294170783943303/1482500000000000000 : ℝ)) (alpha := (85974112411/118600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-359339837/2500000000 : ℝ)*X 0 0+(2709432287/5000000000 : ℝ)*X 0 1+(5418864741/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((328195081/625000000 : ℝ)*X 1 0+(-1672851/10000000 : ℝ)*X 1 1+(338679093/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2625560541/5000000000 : ℝ)*X 2 0+(5418865563/10000000000 : ℝ)*X 2 1+(-418212797/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((449515001/1000000000 : ℝ)*X 0 0+(510970299/1250000000 : ℝ)*X 0 1+(4087762879/10000000000 : ℝ)*X 0 2+(449515001/1000000000 : ℝ)*X 1 0+(510970299/1250000000 : ℝ)*X 1 1+(4087762879/10000000000 : ℝ)*X 1 2+(449515001/1000000000 : ℝ)*X 2 0+(510970299/1250000000 : ℝ)*X 2 1+(4087762879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-249642383/1250000000 : ℝ)*X 0 0+(5213928317/10000000000 : ℝ)*X 0 1+(5213929389/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5392623213/10000000000 : ℝ)*X 1 0+(-1759370427/10000000000 : ℝ)*X 1 1+(2606964751/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((674077953/1250000000 : ℝ)*X 2 0+(5213928379/10000000000 : ℝ)*X 2 1+(-219921423/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3929090401/10000000000 : ℝ)*X 0 0+(2185223693/5000000000 : ℝ)*X 0 1+(546305919/1250000000 : ℝ)*X 0 2+(3929090401/10000000000 : ℝ)*X 1 0+(2185223693/5000000000 : ℝ)*X 1 1+(546305919/1250000000 : ℝ)*X 1 2+(3929090401/10000000000 : ℝ)*X 2 0+(2185223693/5000000000 : ℝ)*X 2 1+(546305919/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1878158851/10000000000 : ℝ)*X 0 0+(1013524677/2000000000 : ℝ)*X 0 1+(1089769043/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1046083129/2000000000 : ℝ)*X 1 0+(-41493233/250000000 : ℝ)*X 1 1+(5448845753/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5230416257/10000000000 : ℝ)*X 2 0+(1362211531/2500000000 : ℝ)*X 2 1+(-829863983/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((142986383/312500000 : ℝ)*X 0 0+(2023166451/5000000000 : ℝ)*X 0 1+(2023165621/5000000000 : ℝ)*X 0 2+(142986383/312500000 : ℝ)*X 1 0+(2023166451/5000000000 : ℝ)*X 1 1+(2023165621/5000000000 : ℝ)*X 1 2+(142986383/312500000 : ℝ)*X 2 0+(2023166451/5000000000 : ℝ)*X 2 1+(2023165621/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-311032693/2000000000 : ℝ)*X 0 0+(1111839413/2000000000 : ℝ)*X 0 1+(5194057273/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1351587483/2500000000 : ℝ)*X 1 0+(-1767456701/10000000000 : ℝ)*X 1 1+(1038811657/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((270317569/500000000 : ℝ)*X 2 0+(5194057337/10000000000 : ℝ)*X 2 1+(-883728003/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1936291183/5000000000 : ℝ)*X 0 0+(4397807689/10000000000 : ℝ)*X 0 1+(34357879/78125000 : ℝ)*X 0 2+(1936291183/5000000000 : ℝ)*X 1 0+(4397807689/10000000000 : ℝ)*X 1 1+(34357879/78125000 : ℝ)*X 1 2+(1936291183/5000000000 : ℝ)*X 2 0+(4397807689/10000000000 : ℝ)*X 2 1+(34357879/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-6491/10000 : ℝ) ≤ (-48112380164953819434869228316051/74125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40088111/25000000000000 : ℝ)*(upper1) + (198313783/100000000000000 : ℝ)*(lower4) + (52915711/50000000000000 : ℝ)*(upper5) + (1675860733129439/100000000000000 : ℝ)*(major0) + (1675860733129439/100000000000000 : ℝ)*(major1) + (1675860733129439/100000000000000 : ℝ)*(major2) + (11433693819/100000000000000 : ℝ)*(sp2) + (3937300821/100000000000000 : ℝ)*(sp3) + (1200586806478649/50000000000000 : ℝ)*(sp4) + (480215852471287/20000000000000 : ℝ)*(sp5) + (4802332663639/200000000000 : ℝ)*(sp6) + (121521932497199/12500000000000 : ℝ)*(sp7) + (4152556021/100000000000000 : ℝ)*(sp12) + (24625789221/25000000000000 : ℝ)*(sp13) + (486089698639207/50000000000000 : ℝ)*(f.failure) + (60029444137833/2500000000000 : ℝ)*(f.sum) + (11774470130979/5930000000000000000000000000 : ℝ)*base65 + (153653637914690483/148250000000000000000000000000000 : ℝ)*base68 + (274522379300559517/148250000000000000000000000000000 : ℝ)*base69 + (360599662967190483/148250000000000000000000000000000 : ℝ)*base72 + (2117582841479/5930000000000000000000000000 : ℝ)*base73 + (745689394446809517/148250000000000000000000000000000 : ℝ)*base75 + (139269299359059517/148250000000000000000000000000000 : ℝ)*base77 + (279924276775809517/148250000000000000000000000000000 : ℝ)*base79 + (20602020496399/5930000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (610011/62500000000000000000 : ℝ)*base89 + (610011/62500000000000000000 : ℝ)*base91 + (610011/62500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (29081/50000 : ℝ) ≤ (10778533820693118352005445472589/18531250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (100929713/100000000000000 : ℝ)*(upper2) + (3896403/20000000000000 : ℝ)*(upper4) + (639213/3125000000000 : ℝ)*(upper5) + (440056427333993/25000000000000 : ℝ)*(major0) + (440056427333993/25000000000000 : ℝ)*(major1) + (440056427333993/25000000000000 : ℝ)*(major2) + (123997051227317/5000000000000 : ℝ)*(sp0) + (247993177086313/10000000000000 : ℝ)*(sp1) + (2479933776313339/100000000000000 : ℝ)*(sp2) + (510557479455561/50000000000000 : ℝ)*(sp3) + (2292526519/20000000000000 : ℝ)*(sp5) + (4728591193/50000000000000 : ℝ)*(sp6) + (2597329781/50000000000000 : ℝ)*(sp11) + (441789877/20000000000000 : ℝ)*(sp12) + (255280038392671/25000000000000 : ℝ)*(f.failure) + (1239971616747863/50000000000000 : ℝ)*(f.sum) + (1284759505609/2965000000000000000000000000 : ℝ)*base66 + (349268885341323879/37062500000000000000000000000000 : ℝ)*base67 + (390265408346198879/37062500000000000000000000000000 : ℝ)*base69 + (113546775729948879/37062500000000000000000000000000 : ℝ)*base71 + (15556698639151/2965000000000000000000000000 : ℝ)*base73 + (368352202070886379/37062500000000000000000000000000 : ℝ)*base75 + (493461289475511379/37062500000000000000000000000000 : ℝ)*base77 + (294562301663948879/37062500000000000000000000000000 : ℝ)*base79 + (334554302657/370625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (381317/31250000000000000000 : ℝ)*base90 + (381317/31250000000000000000 : ℝ)*base92 + (381317/31250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (40187/50000 : ℝ) ≤ (29789358066311256852893665976871/37062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20569739/20000000000000 : ℝ)*(lower3) + (398606497/100000000000000 : ℝ)*(upper4) + (19572209/25000000000000 : ℝ)*(lower5) + (1866304352000831/100000000000000 : ℝ)*(major0) + (1866304352000831/100000000000000 : ℝ)*(major1) + (1866304352000831/100000000000000 : ℝ)*(major2) + (775606947/10000000000000 : ℝ)*(sp0) + (22283637393/25000000000000 : ℝ)*(sp1) + (204120547221/100000000000000 : ℝ)*(sp2) + (8184174153/10000000000000 : ℝ)*(sp3) + (512334330923/19531250000 : ℝ)*(sp8) + (2623070395845659/100000000000000 : ℝ)*(sp9) + (262295540984801/10000000000000 : ℝ)*(sp10) + (1082575329107111/100000000000000 : ℝ)*(sp11) + (1082657170848641/100000000000000 : ℝ)*(f.failure) + (262315953039523/10000000000000 : ℝ)*(f.sum) + (37453383694739/5930000000000000000000000000 : ℝ)*base66 + (1641154933190647293/148250000000000000000000000000000 : ℝ)*base67 + (1643132122685647293/148250000000000000000000000000000 : ℝ)*base69 + (199798863522602707/148250000000000000000000000000000 : ℝ)*base72 + (34937212241681/5930000000000000000000000000 : ℝ)*base73 + (892273789198397293/148250000000000000000000000000000 : ℝ)*base75 + (358081997546147293/148250000000000000000000000000000 : ℝ)*base77 + (327658408735897293/148250000000000000000000000000000 : ℝ)*base79 + (3800451406221/5930000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (36507/125000000000000000000 : ℝ)*base90 + (36507/125000000000000000000 : ℝ)*base92 + (36507/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-87793/100000 : ℝ) ≤ (-3253753165554034524139520269203/3706250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11647131/6250000000000 : ℝ)*(lower1) + (321865319/100000000000000 : ℝ)*(lower2) + (139069321/100000000000000 : ℝ)*(upper5) + (95409248394267/5000000000000 : ℝ)*(major0) + (95409248394267/5000000000000 : ℝ)*(major1) + (95409248394267/5000000000000 : ℝ)*(major2) + (1376531657/20000000000000 : ℝ)*(sp0) + (32170581509/100000000000000 : ℝ)*(sp5) + (43290165957/50000000000000 : ℝ)*(sp6) + (117805839/50000000000000 : ℝ)*(sp7) + (684668570545687/25000000000000 : ℝ)*(sp12) + (109545959770381/4000000000000 : ℝ)*(sp13) + (8558108076591/312500000000 : ℝ)*(sp14) + (1106952195041887/100000000000000 : ℝ)*(sp15) + (221390486130713/20000000000000 : ℝ)*(f.failure) + (1369340582420517/50000000000000 : ℝ)*(f.sum) + (114288178057/296500000000000000000000000 : ℝ)*base65 + (68986128150293901/7412500000000000000000000000000 : ℝ)*base67 + (56941548538993901/7412500000000000000000000000000 : ℝ)*base69 + (4505048783193901/7412500000000000000000000000000 : ℝ)*base71 + (664058435211/118600000000000000000000000 : ℝ)*base73 + (2615203812531099/7412500000000000000000000000000 : ℝ)*base76 + (17728569122356401/7412500000000000000000000000000 : ℝ)*base77 + (11914420439056099/7412500000000000000000000000000 : ℝ)*base80 + (537308400599/296500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (156851/25000000000000000000 : ℝ)*base90 + (156851/25000000000000000000 : ℝ)*base92 + (156851/25000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1607_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2154773/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8173/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (651/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6491/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(29081/50000 : ℝ) else (40187/50000 : ℝ) ≤ X j i ∧ X j i ≤ (87793/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1607_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1607_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2154773/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8173/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (651/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6491/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(29081/50000 : ℝ) else (40187/50000 : ℝ) ≤ X j i ∧ X j i ≤ (87793/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1607_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2154773/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8173/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (651/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6491/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(29081/50000 : ℝ) else (40187/50000 : ℝ) ≤ X j i ∧ X j i ≤ (87793/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1607_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

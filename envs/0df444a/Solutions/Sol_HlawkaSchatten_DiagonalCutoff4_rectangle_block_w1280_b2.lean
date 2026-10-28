-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1280_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:22:59.227389+00:00
-- url     : https://prove2.me/submissions/7f57ccf1-e6c6-48d4-a962-dc3c009149b5

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
theorem support_rectangle_w1280_s6_0 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2098762957/10000000000 : ℝ)*x 0 + (1083189757/2000000000 : ℝ)*x 1 + (5242455369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2098762957/10000000000 : ℝ)^265 ≤ (6383239519389/50000000000000 : ℝ)^201 := by
    have hnat : (2098762957 : ℕ)^265*50000000000000^201 ≤ 6383239519389^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098762957 10000000000 6383239519389 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083189757/2000000000 : ℝ)^265 ≤ (5569092331389/12500000000000 : ℝ)^201 := by
    have hnat : (1083189757 : ℕ)^265*12500000000000^201 ≤ 5569092331389^201*2000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083189757 2000000000 5569092331389 12500000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242455369/10000000000 : ℝ)^265 ≤ (21340391151673/50000000000000 : ℝ)^201 := by
    have hnat : (5242455369 : ℕ)^265*50000000000000^201 ≤ 21340391151673^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242455369 10000000000 21340391151673 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2098762957/10000000000 : ℝ), (1083189757/2000000000 : ℝ), (5242455369/10000000000 : ℝ)] ![(6383239519389/50000000000000 : ℝ), (5569092331389/12500000000000 : ℝ), (21340391151673/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2098762957/10000000000 : ℝ)|^265 ≤ (6383239519389/50000000000000 : ℝ)^201
        have hw : |(-2098762957/10000000000 : ℝ)|=(2098762957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083189757/2000000000 : ℝ)|^265 ≤ (5569092331389/12500000000000 : ℝ)^201
        have hw : |(1083189757/2000000000 : ℝ)|=(1083189757/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242455369/10000000000 : ℝ)|^265 ≤ (21340391151673/50000000000000 : ℝ)^201
        have hw : |(5242455369/10000000000 : ℝ)|=(5242455369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s6_1 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (83593461/156250000 : ℝ)*x 0 + (-2187213073/10000000000 : ℝ)*x 1 + (41939643/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83593461/156250000 : ℝ)^265 ≤ (21919340779719/50000000000000 : ℝ)^201 := by
    have hnat : (83593461 : ℕ)^265*50000000000000^201 ≤ 21919340779719^201*156250000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83593461 156250000 21919340779719 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2187213073/10000000000 : ℝ)^265 ≤ (2696107211759/20000000000000 : ℝ)^201 := by
    have hnat : (2187213073 : ℕ)^265*20000000000000^201 ≤ 2696107211759^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187213073 10000000000 2696107211759 20000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41939643/80000000 : ℝ)^265 ≤ (10670195591937/25000000000000 : ℝ)^201 := by
    have hnat : (41939643 : ℕ)^265*25000000000000^201 ≤ 10670195591937^201*80000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41939643 80000000 10670195591937 25000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83593461/156250000 : ℝ), (-2187213073/10000000000 : ℝ), (41939643/80000000 : ℝ)] ![(21919340779719/50000000000000 : ℝ), (2696107211759/20000000000000 : ℝ), (10670195591937/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83593461/156250000 : ℝ)|^265 ≤ (21919340779719/50000000000000 : ℝ)^201
        have hw : |(83593461/156250000 : ℝ)|=(83593461/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2187213073/10000000000 : ℝ)|^265 ≤ (2696107211759/20000000000000 : ℝ)^201
        have hw : |(-2187213073/10000000000 : ℝ)|=(2187213073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41939643/80000000 : ℝ)|^265 ≤ (10670195591937/25000000000000 : ℝ)^201
        have hw : |(41939643/80000000 : ℝ)|=(41939643/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s6_2 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5349981479/10000000000 : ℝ)*x 0 + (655306923/1250000000 : ℝ)*x 1 + (-437442619/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349981479/10000000000 : ℝ)^265 ≤ (43838681289357/100000000000000 : ℝ)^201 := by
    have hnat : (5349981479 : ℕ)^265*100000000000000^201 ≤ 43838681289357^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349981479 10000000000 43838681289357 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655306923/1250000000 : ℝ)^265 ≤ (42680782464351/100000000000000 : ℝ)^201 := by
    have hnat : (655306923 : ℕ)^265*100000000000000^201 ≤ 42680782464351^201*1250000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655306923 1250000000 42680782464351 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (437442619/2000000000 : ℝ)^265 ≤ (13480536237563/100000000000000 : ℝ)^201 := by
    have hnat : (437442619 : ℕ)^265*100000000000000^201 ≤ 13480536237563^201*2000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437442619 2000000000 13480536237563 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349981479/10000000000 : ℝ), (655306923/1250000000 : ℝ), (-437442619/2000000000 : ℝ)] ![(43838681289357/100000000000000 : ℝ), (42680782464351/100000000000000 : ℝ), (13480536237563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349981479/10000000000 : ℝ)|^265 ≤ (43838681289357/100000000000000 : ℝ)^201
        have hw : |(5349981479/10000000000 : ℝ)|=(5349981479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655306923/1250000000 : ℝ)|^265 ≤ (42680782464351/100000000000000 : ℝ)^201
        have hw : |(655306923/1250000000 : ℝ)|=(655306923/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-437442619/2000000000 : ℝ)|^265 ≤ (13480536237563/100000000000000 : ℝ)^201
        have hw : |(-437442619/2000000000 : ℝ)|=(437442619/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s6_3 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4343090597/10000000000 : ℝ)*x 0 + (130284613/312500000 : ℝ)*x 1 + (4524043459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4343090597/10000000000 : ℝ)^265 ≤ (33302065592317/100000000000000 : ℝ)^201 := by
    have hnat : (4343090597 : ℕ)^265*100000000000000^201 ≤ 33302065592317^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4343090597 10000000000 33302065592317 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130284613/312500000 : ℝ)^265 ≤ (3155453654439/10000000000000 : ℝ)^201 := by
    have hnat : (130284613 : ℕ)^265*10000000000000^201 ≤ 3155453654439^201*312500000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130284613 312500000 3155453654439 10000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4524043459/10000000000 : ℝ)^265 ≤ (1757169892683/5000000000000 : ℝ)^201 := by
    have hnat : (4524043459 : ℕ)^265*5000000000000^201 ≤ 1757169892683^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4524043459 10000000000 1757169892683 5000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4343090597/10000000000 : ℝ), (130284613/312500000 : ℝ), (4524043459/10000000000 : ℝ)] ![(33302065592317/100000000000000 : ℝ), (3155453654439/10000000000000 : ℝ), (1757169892683/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4343090597/10000000000 : ℝ)|^265 ≤ (33302065592317/100000000000000 : ℝ)^201
        have hw : |(4343090597/10000000000 : ℝ)|=(4343090597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(130284613/312500000 : ℝ)|^265 ≤ (3155453654439/10000000000000 : ℝ)^201
        have hw : |(130284613/312500000 : ℝ)|=(130284613/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4524043459/10000000000 : ℝ)|^265 ≤ (1757169892683/5000000000000 : ℝ)^201
        have hw : |(4524043459/10000000000 : ℝ)|=(4524043459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s6_4 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-41975517/200000000 : ℝ)*x 0 + (5243073891/10000000000 : ℝ)*x 1 + (1353831771/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41975517/200000000 : ℝ)^265 ≤ (6383291218369/50000000000000 : ℝ)^201 := by
    have hnat : (41975517 : ℕ)^265*50000000000000^201 ≤ 6383291218369^201*200000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41975517 200000000 6383291218369 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243073891/10000000000 : ℝ)^265 ≤ (21343710713477/50000000000000 : ℝ)^201 := by
    have hnat : (5243073891 : ℕ)^265*50000000000000^201 ≤ 21343710713477^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243073891 10000000000 21343710713477 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353831771/2500000000 : ℝ)^265 ≤ (44545996114681/100000000000000 : ℝ)^201 := by
    have hnat : (1353831771 : ℕ)^265*100000000000000^201 ≤ 44545996114681^201*2500000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353831771 2500000000 44545996114681 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-41975517/200000000 : ℝ), (5243073891/10000000000 : ℝ), (1353831771/2500000000 : ℝ)] ![(6383291218369/50000000000000 : ℝ), (21343710713477/50000000000000 : ℝ), (44545996114681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-41975517/200000000 : ℝ)|^265 ≤ (6383291218369/50000000000000 : ℝ)^201
        have hw : |(-41975517/200000000 : ℝ)|=(41975517/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243073891/10000000000 : ℝ)|^265 ≤ (21343710713477/50000000000000 : ℝ)^201
        have hw : |(5243073891/10000000000 : ℝ)|=(5243073891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353831771/2500000000 : ℝ)|^265 ≤ (44545996114681/100000000000000 : ℝ)^201
        have hw : |(1353831771/2500000000 : ℝ)|=(1353831771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s6_5 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2652815447/5000000000 : ℝ)*x 0 + (-251792673/1250000000 : ℝ)*x 1 + (135383177/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652815447/5000000000 : ℝ)^265 ≤ (43360183719373/100000000000000 : ℝ)^201 := by
    have hnat : (2652815447 : ℕ)^265*100000000000000^201 ≤ 43360183719373^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652815447 5000000000 43360183719373 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (251792673/1250000000 : ℝ)^265 ≤ (6046910094037/50000000000000 : ℝ)^201 := by
    have hnat : (251792673 : ℕ)^265*50000000000000^201 ≤ 6046910094037^201*1250000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251792673 1250000000 6046910094037 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135383177/250000000 : ℝ)^265 ≤ (44545996071301/100000000000000 : ℝ)^201 := by
    have hnat : (135383177 : ℕ)^265*100000000000000^201 ≤ 44545996071301^201*250000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135383177 250000000 44545996071301 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652815447/5000000000 : ℝ), (-251792673/1250000000 : ℝ), (135383177/250000000 : ℝ)] ![(43360183719373/100000000000000 : ℝ), (6046910094037/50000000000000 : ℝ), (44545996071301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652815447/5000000000 : ℝ)|^265 ≤ (43360183719373/100000000000000 : ℝ)^201
        have hw : |(2652815447/5000000000 : ℝ)|=(2652815447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-251792673/1250000000 : ℝ)|^265 ≤ (6046910094037/50000000000000 : ℝ)^201
        have hw : |(-251792673/1250000000 : ℝ)|=(251792673/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135383177/250000000 : ℝ)|^265 ≤ (44545996071301/100000000000000 : ℝ)^201
        have hw : |(135383177/250000000 : ℝ)|=(135383177/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s6_6 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (530563089/1000000000 : ℝ)*x 0 + (5415327081/10000000000 : ℝ)*x 1 + (-201434139/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530563089/1000000000 : ℝ)^265 ≤ (1734407347051/4000000000000 : ℝ)^201 := by
    have hnat : (530563089 : ℕ)^265*4000000000000^201 ≤ 1734407347051^201*1000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530563089 1000000000 1734407347051 4000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415327081/10000000000 : ℝ)^265 ≤ (22272998041073/50000000000000 : ℝ)^201 := by
    have hnat : (5415327081 : ℕ)^265*50000000000000^201 ≤ 22272998041073^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415327081 10000000000 22272998041073 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (201434139/1000000000 : ℝ)^265 ≤ (12093820235567/100000000000000 : ℝ)^201 := by
    have hnat : (201434139 : ℕ)^265*100000000000000^201 ≤ 12093820235567^201*1000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201434139 1000000000 12093820235567 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530563089/1000000000 : ℝ), (5415327081/10000000000 : ℝ), (-201434139/1000000000 : ℝ)] ![(1734407347051/4000000000000 : ℝ), (22272998041073/50000000000000 : ℝ), (12093820235567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530563089/1000000000 : ℝ)|^265 ≤ (1734407347051/4000000000000 : ℝ)^201
        have hw : |(530563089/1000000000 : ℝ)|=(530563089/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415327081/10000000000 : ℝ)|^265 ≤ (22272998041073/50000000000000 : ℝ)^201
        have hw : |(5415327081/10000000000 : ℝ)|=(5415327081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-201434139/1000000000 : ℝ)|^265 ≤ (12093820235567/100000000000000 : ℝ)^201
        have hw : |(-201434139/1000000000 : ℝ)|=(201434139/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s6_7 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4343116971/10000000000 : ℝ)*x 0 + (4522778083/10000000000 : ℝ)*x 1 + (4170379503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4343116971/10000000000 : ℝ)^265 ≤ (8325583053969/25000000000000 : ℝ)^201 := by
    have hnat : (4343116971 : ℕ)^265*25000000000000^201 ≤ 8325583053969^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4343116971 10000000000 8325583053969 25000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4522778083/10000000000 : ℝ)^265 ≤ (35130438986141/100000000000000 : ℝ)^201 := by
    have hnat : (4522778083 : ℕ)^265*100000000000000^201 ≤ 35130438986141^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4522778083 10000000000 35130438986141 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4170379503/10000000000 : ℝ)^265 ≤ (31567228780323/100000000000000 : ℝ)^201 := by
    have hnat : (4170379503 : ℕ)^265*100000000000000^201 ≤ 31567228780323^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170379503 10000000000 31567228780323 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4343116971/10000000000 : ℝ), (4522778083/10000000000 : ℝ), (4170379503/10000000000 : ℝ)] ![(8325583053969/25000000000000 : ℝ), (35130438986141/100000000000000 : ℝ), (31567228780323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4343116971/10000000000 : ℝ)|^265 ≤ (8325583053969/25000000000000 : ℝ)^201
        have hw : |(4343116971/10000000000 : ℝ)|=(4343116971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4522778083/10000000000 : ℝ)|^265 ≤ (35130438986141/100000000000000 : ℝ)^201
        have hw : |(4522778083/10000000000 : ℝ)|=(4522778083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4170379503/10000000000 : ℝ)|^265 ≤ (31567228780323/100000000000000 : ℝ)^201
        have hw : |(4170379503/10000000000 : ℝ)|=(4170379503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1280_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152290869/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14679/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5491/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2199/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7333/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14679/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5491/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14679/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5491/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14679/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5491/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14679/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5491/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14679/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5491/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14679/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5491/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5491/50000 : ℝ) ^ (4239/1024 : ℝ) ≤ (2671150930829783/25000000000000000000 : ℝ) := by
    have hpowers : (5491/50000 : ℝ)^4239 ≤ (2671150930829783/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5491 : ℕ)^4239*25000000000000000000^1024 ≤ 2671150930829783^1024*50000^4239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5491 50000 2671150930829783 25000000000000000000 4239 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5491/50000 : ℝ)) (X := (2671150930829783/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14679/100000 : ℝ) ^ (4239/1024 : ℝ) ≤ (35515370207336609/100000000000000000000 : ℝ) := by
    have hpowers : (14679/100000 : ℝ)^4239 ≤ (35515370207336609/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14679 : ℕ)^4239*100000000000000000000^1024 ≤ 35515370207336609^1024*100000^4239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14679 100000 35515370207336609 100000000000000000000 4239 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14679/100000 : ℝ)) (X := (35515370207336609/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502671150930829783/12500000000000000000 : ℝ) ≤ (10000516166440679/10000000000000000 : ℝ) ^ (4239/1024 : ℝ) := by
    have hpowers : (12502671150930829783/12500000000000000000 : ℝ)^1024 ≤ (10000516166440679/10000000000000000 : ℝ)^4239 := by
      have hnat : (12502671150930829783 : ℕ)^1024*10000000000000000^4239 ≤ 10000516166440679^4239*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502671150930829783 12500000000000000000 10000516166440679 10000000000000000 1024 4239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000516166440679/10000000000000000 : ℝ)) (X := (12502671150930829783/12500000000000000000 : ℝ)) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046199973930655741/100000000000000000000 : ℝ) ≤ (10001115840696943/10000000000000000 : ℝ) ^ (4239/1024 : ℝ) := by
    have hpowers : (100046199973930655741/100000000000000000000 : ℝ)^1024 ≤ (10001115840696943/10000000000000000 : ℝ)^4239 := by
      have hnat : (100046199973930655741 : ℕ)^1024*10000000000000000^4239 ≤ 10001115840696943^4239*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046199973930655741 100000000000000000000 10001115840696943 10000000000000000 1024 4239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001115840696943/10000000000000000 : ℝ)) (X := (100046199973930655741/100000000000000000000 : ℝ)) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035515370207336609/50000000000000000000 : ℝ) ≤ (10001715514953207/10000000000000000 : ℝ) ^ (4239/1024 : ℝ) := by
    have hpowers : (50035515370207336609/50000000000000000000 : ℝ)^1024 ≤ (10001715514953207/10000000000000000 : ℝ)^4239 := by
      have hnat : (50035515370207336609 : ℕ)^1024*10000000000000000^4239 ≤ 10001715514953207^4239*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035515370207336609 50000000000000000000 10001715514953207 10000000000000000 1024 4239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001715514953207/10000000000000000 : ℝ)) (X := (50035515370207336609/50000000000000000000 : ℝ)) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2671150930829783/25000000000000000000 : ℝ) ≤ ((36958737021966607767/36970000000000000000 : ℝ)+2*(74959282033/46212500000000 : ℝ)*(5491/50000 : ℝ))^(4239/1024 : ℝ) := by
    rw [show (36958737021966607767/36970000000000000000 : ℝ)+2*(74959282033/46212500000000 : ℝ)*(5491/50000 : ℝ)=(10000516166440679/10000000000000000 : ℝ) by norm_num, show 1+2*(2671150930829783/25000000000000000000 : ℝ)=(12502671150930829783/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35515370207336609/100000000000000000000 : ℝ)+(2671150930829783/25000000000000000000 : ℝ) ≤ ((36958737021966607767/36970000000000000000 : ℝ)+(74959282033/46212500000000 : ℝ)*((14679/100000 : ℝ)+(5491/50000 : ℝ)))^(4239/1024 : ℝ) := by
    rw [show (36958737021966607767/36970000000000000000 : ℝ)+(74959282033/46212500000000 : ℝ)*((14679/100000 : ℝ)+(5491/50000 : ℝ))=(10001115840696943/10000000000000000 : ℝ) by norm_num, show 1+(35515370207336609/100000000000000000000 : ℝ)+(2671150930829783/25000000000000000000 : ℝ)=(100046199973930655741/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35515370207336609/100000000000000000000 : ℝ) ≤ ((36958737021966607767/36970000000000000000 : ℝ)+2*(74959282033/46212500000000 : ℝ)*(14679/100000 : ℝ))^(4239/1024 : ℝ) := by
    rw [show (36958737021966607767/36970000000000000000 : ℝ)+2*(74959282033/46212500000000 : ℝ)*(14679/100000 : ℝ)=(10001715514953207/10000000000000000 : ℝ) by norm_num, show 1+2*(35515370207336609/100000000000000000000 : ℝ)=(50035515370207336609/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36958737021966607767/36970000000000000000 : ℝ)*(X 1 0+X 2 0)+(74959282033/46212500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4239/1024 : ℝ)) (lo := (5491/50000 : ℝ)) (hi := (14679/100000 : ℝ)) (c := (36958737021966607767/36970000000000000000 : ℝ)) (alpha := (74959282033/46212500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36958737021966607767/36970000000000000000 : ℝ)*(X 0 1+X 2 1)+(74959282033/46212500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4239/1024 : ℝ)) (lo := (5491/50000 : ℝ)) (hi := (14679/100000 : ℝ)) (c := (36958737021966607767/36970000000000000000 : ℝ)) (alpha := (74959282033/46212500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36958737021966607767/36970000000000000000 : ℝ)*(X 0 2+X 1 2)+(74959282033/46212500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4239/1024 : ℝ)) (lo := (5491/50000 : ℝ)) (hi := (14679/100000 : ℝ)) (c := (36958737021966607767/36970000000000000000 : ℝ)) (alpha := (74959282033/46212500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2098762957/10000000000 : ℝ)*X 0 0+(1083189757/2000000000 : ℝ)*X 0 1+(5242455369/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((83593461/156250000 : ℝ)*X 1 0+(-2187213073/10000000000 : ℝ)*X 1 1+(41939643/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349981479/10000000000 : ℝ)*X 2 0+(655306923/1250000000 : ℝ)*X 2 1+(-437442619/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4343090597/10000000000 : ℝ)*X 0 0+(130284613/312500000 : ℝ)*X 0 1+(4524043459/10000000000 : ℝ)*X 0 2+(4343090597/10000000000 : ℝ)*X 1 0+(130284613/312500000 : ℝ)*X 1 1+(4524043459/10000000000 : ℝ)*X 1 2+(4343090597/10000000000 : ℝ)*X 2 0+(130284613/312500000 : ℝ)*X 2 1+(4524043459/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-41975517/200000000 : ℝ)*X 0 0+(5243073891/10000000000 : ℝ)*X 0 1+(1353831771/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652815447/5000000000 : ℝ)*X 1 0+(-251792673/1250000000 : ℝ)*X 1 1+(135383177/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530563089/1000000000 : ℝ)*X 2 0+(5415327081/10000000000 : ℝ)*X 2 1+(-201434139/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4343116971/10000000000 : ℝ)*X 0 0+(4522778083/10000000000 : ℝ)*X 0 1+(4170379503/10000000000 : ℝ)*X 0 2+(4343116971/10000000000 : ℝ)*X 1 0+(4522778083/10000000000 : ℝ)*X 1 1+(4170379503/10000000000 : ℝ)*X 1 2+(4343116971/10000000000 : ℝ)*X 2 0+(4522778083/10000000000 : ℝ)*X 2 1+(4170379503/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1770226519502448574372821699/924250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (202981213/50000000000000 : ℝ)*(base19) + (45109901/12500000000000 : ℝ)*(base23) + (9709627/100000000000000 : ℝ)*(lower2) + (61625033/100000000000000 : ℝ)*(upper3) + (695871/4000000000000 : ℝ)*(upper5) + (4290671855129999/100000000000000 : ℝ)*(major0) + (4290671855129999/100000000000000 : ℝ)*(major1) + (429067185513/10000000000 : ℝ)*(major2) + (5763916854117717/100000000000000 : ℝ)*(sp0) + (2881962127890259/50000000000000 : ℝ)*(sp1) + (1152784860172747/20000000000000 : ℝ)*(sp2) + (2817414461665871/100000000000000 : ℝ)*(sp3) + (7807625227/100000000000000 : ℝ)*(sp4) + (904601493/20000000000000 : ℝ)*(sp7) + (352177373084167/12500000000000 : ℝ)*(f.failure) + (180122645679467/3125000000000 : ℝ)*(f.sum) + (29895814997887/18485000000000000000000000000 : ℝ)*base66 + (26808733289572897767/3697000000000000000000000000000000 : ℝ)*base68 + (975828084435669/369700000000000000000000000000 : ℝ)*base70 + (18081622229249897767/3697000000000000000000000000000000 : ℝ)*base72 + (23142734597123/18485000000000000000000000000 : ℝ)*base73 + (5659913630682969/369700000000000000000000000000 : ℝ)*base76 + (16549014453997297767/3697000000000000000000000000000000 : ℝ)*base78 + (39332497144385297767/3697000000000000000000000000000000 : ℝ)*base80 + (30726938309879/18485000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (15071123/1250000000000000000000 : ℝ)*base89 + (15071123/1250000000000000000000 : ℝ)*base91 + (2571123/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2357765793739679402591912721/462125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (464940909/50000000000000 : ℝ)*(base19) + (992963761/100000000000000 : ℝ)*(base23) + (20706787/20000000000000 : ℝ)*(upper3) + (31202317/100000000000000 : ℝ)*(lower4) + (102977663/100000000000000 : ℝ)*(upper5) + (1080387842753421/25000000000000 : ℝ)*(major0) + (1080387842753421/25000000000000 : ℝ)*(major1) + (1080387842753421/25000000000000 : ℝ)*(major2) + (18537695541/100000000000000 : ℝ)*(sp1) + (3914473619/20000000000000 : ℝ)*(sp2) + (1451351729496363/25000000000000 : ℝ)*(sp4) + (5805387450408093/100000000000000 : ℝ)*(sp5) + (1451346588163399/25000000000000 : ℝ)*(sp6) + (56753913079499/2000000000000 : ℝ)*(sp7) + (56753913079499/2000000000000 : ℝ)*(f.failure) + (1451351729496363/25000000000000 : ℝ)*(f.sum) + (1886854612663/9242500000000000000000000000 : ℝ)*base65 + (7515846982094679093/924250000000000000000000000000000 : ℝ)*base68 + (3538963042467679093/924250000000000000000000000000000 : ℝ)*base70 + (4754207090039179093/924250000000000000000000000000000 : ℝ)*base72 + (71250443326249/18485000000000000000000000000 : ℝ)*base74 + (17562164156067570907/924250000000000000000000000000000 : ℝ)*base75 + (5813672826990070907/924250000000000000000000000000000 : ℝ)*base77 + (16937996249526679093/924250000000000000000000000000000 : ℝ)*base80 + (144312678295149/18485000000000000000000000000 : ℝ)*base82 + (794631/200000000000000000000 : ℝ)*base89 + (794631/200000000000000000000 : ℝ)*base91 + (794631/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1280_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152290869/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14679/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5491/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2199/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7333/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1280_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1280_s7_0 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1049387249/5000000000 : ℝ)*x 0 + (5415830121/10000000000 : ℝ)*x 1 + (1048513329/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049387249/5000000000 : ℝ)^265 ≤ (12766571594097/100000000000000 : ℝ)^201 := by
    have hnat : (1049387249 : ℕ)^265*100000000000000^201 ≤ 12766571594097^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049387249 5000000000 12766571594097 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415830121/10000000000 : ℝ)^265 ≤ (44551451684911/100000000000000 : ℝ)^201 := by
    have hnat : (5415830121 : ℕ)^265*100000000000000^201 ≤ 44551451684911^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415830121 10000000000 44551451684911 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048513329/2000000000 : ℝ)^265 ≤ (42681976705063/100000000000000 : ℝ)^201 := by
    have hnat : (1048513329 : ℕ)^265*100000000000000^201 ≤ 42681976705063^201*2000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048513329 2000000000 42681976705063 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1049387249/5000000000 : ℝ), (5415830121/10000000000 : ℝ), (1048513329/2000000000 : ℝ)] ![(12766571594097/100000000000000 : ℝ), (44551451684911/100000000000000 : ℝ), (42681976705063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1049387249/5000000000 : ℝ)|^265 ≤ (12766571594097/100000000000000 : ℝ)^201
        have hw : |(-1049387249/5000000000 : ℝ)|=(1049387249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415830121/10000000000 : ℝ)|^265 ≤ (44551451684911/100000000000000 : ℝ)^201
        have hw : |(5415830121/10000000000 : ℝ)|=(5415830121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048513329/2000000000 : ℝ)|^265 ≤ (42681976705063/100000000000000 : ℝ)^201
        have hw : |(1048513329/2000000000 : ℝ)|=(1048513329/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s7_1 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (668743969/1250000000 : ℝ)*x 0 + (-1093552499/5000000000 : ℝ)*x 1 + (1048513427/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668743969/1250000000 : ℝ)^265 ≤ (43838360140989/100000000000000 : ℝ)^201 := by
    have hnat : (668743969 : ℕ)^265*100000000000000^201 ≤ 43838360140989^201*1250000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668743969 1250000000 43838360140989 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1093552499/5000000000 : ℝ)^265 ≤ (336991446759/2500000000000 : ℝ)^201 := by
    have hnat : (1093552499 : ℕ)^265*2500000000000^201 ≤ 336991446759^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093552499 5000000000 336991446759 2500000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048513427/2000000000 : ℝ)^265 ≤ (10670495491147/25000000000000 : ℝ)^201 := by
    have hnat : (1048513427 : ℕ)^265*25000000000000^201 ≤ 10670495491147^201*2000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048513427 2000000000 10670495491147 25000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668743969/1250000000 : ℝ), (-1093552499/5000000000 : ℝ), (1048513427/2000000000 : ℝ)] ![(43838360140989/100000000000000 : ℝ), (336991446759/2500000000000 : ℝ), (10670495491147/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668743969/1250000000 : ℝ)|^265 ≤ (43838360140989/100000000000000 : ℝ)^201
        have hw : |(668743969/1250000000 : ℝ)|=(668743969/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1093552499/5000000000 : ℝ)|^265 ≤ (336991446759/2500000000000 : ℝ)^201
        have hw : |(-1093552499/5000000000 : ℝ)|=(1093552499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048513427/2000000000 : ℝ)|^265 ≤ (10670495491147/25000000000000 : ℝ)^201
        have hw : |(1048513427/2000000000 : ℝ)|=(1048513427/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s7_2 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1069990373/2000000000 : ℝ)*x 0 + (5242565607/10000000000 : ℝ)*x 1 + (-2187106867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069990373/2000000000 : ℝ)^265 ≤ (10959590340439/25000000000000 : ℝ)^201 := by
    have hnat : (1069990373 : ℕ)^265*25000000000000^201 ≤ 10959590340439^201*2000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069990373 2000000000 10959590340439 25000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242565607/10000000000 : ℝ)^265 ≤ (42681965563459/100000000000000 : ℝ)^201 := by
    have hnat : (5242565607 : ℕ)^265*100000000000000^201 ≤ 42681965563459^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242565607 10000000000 42681965563459 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2187106867/10000000000 : ℝ)^265 ≤ (2695934611447/20000000000000 : ℝ)^201 := by
    have hnat : (2187106867 : ℕ)^265*20000000000000^201 ≤ 2695934611447^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187106867 10000000000 2695934611447 20000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069990373/2000000000 : ℝ), (5242565607/10000000000 : ℝ), (-2187106867/10000000000 : ℝ)] ![(10959590340439/25000000000000 : ℝ), (42681965563459/100000000000000 : ℝ), (2695934611447/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069990373/2000000000 : ℝ)|^265 ≤ (10959590340439/25000000000000 : ℝ)^201
        have hw : |(1069990373/2000000000 : ℝ)|=(1069990373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242565607/10000000000 : ℝ)|^265 ≤ (42681965563459/100000000000000 : ℝ)^201
        have hw : |(5242565607/10000000000 : ℝ)|=(5242565607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2187106867/10000000000 : ℝ)|^265 ≤ (2695934611447/20000000000000 : ℝ)^201
        have hw : |(-2187106867/10000000000 : ℝ)|=(2187106867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s7_3 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4343097113/10000000000 : ℝ)*x 0 + (1042335627/2500000000 : ℝ)*x 1 + (2261904081/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4343097113/10000000000 : ℝ)^265 ≤ (6660426292937/20000000000000 : ℝ)^201 := by
    have hnat : (4343097113 : ℕ)^265*20000000000000^201 ≤ 6660426292937^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4343097113 10000000000 6660426292937 20000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042335627/2500000000 : ℝ)^265 ≤ (7889220113201/25000000000000 : ℝ)^201 := by
    have hnat : (1042335627 : ℕ)^265*25000000000000^201 ≤ 7889220113201^201*2500000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042335627 2500000000 7889220113201 25000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2261904081/5000000000 : ℝ)^265 ≤ (8785247015369/25000000000000 : ℝ)^201 := by
    have hnat : (2261904081 : ℕ)^265*25000000000000^201 ≤ 8785247015369^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261904081 5000000000 8785247015369 25000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4343097113/10000000000 : ℝ), (1042335627/2500000000 : ℝ), (2261904081/5000000000 : ℝ)] ![(6660426292937/20000000000000 : ℝ), (7889220113201/25000000000000 : ℝ), (8785247015369/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4343097113/10000000000 : ℝ)|^265 ≤ (6660426292937/20000000000000 : ℝ)^201
        have hw : |(4343097113/10000000000 : ℝ)|=(4343097113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1042335627/2500000000 : ℝ)|^265 ≤ (7889220113201/25000000000000 : ℝ)^201
        have hw : |(1042335627/2500000000 : ℝ)|=(1042335627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2261904081/5000000000 : ℝ)|^265 ≤ (8785247015369/25000000000000 : ℝ)^201
        have hw : |(2261904081/5000000000 : ℝ)|=(2261904081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s7_4 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2098786827/10000000000 : ℝ)*x 0 + (1310795953/2500000000 : ℝ)*x 1 + (1353802543/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2098786827/10000000000 : ℝ)^265 ≤ (12766670469117/100000000000000 : ℝ)^201 := by
    have hnat : (2098786827 : ℕ)^265*100000000000000^201 ≤ 12766670469117^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098786827 10000000000 12766670469117 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310795953/2500000000 : ℝ)^265 ≤ (42688601328799/100000000000000 : ℝ)^201 := by
    have hnat : (1310795953 : ℕ)^265*100000000000000^201 ≤ 42688601328799^201*2500000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310795953 2500000000 42688601328799 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353802543/2500000000 : ℝ)^265 ≤ (22272364098007/50000000000000 : ℝ)^201 := by
    have hnat : (1353802543 : ℕ)^265*50000000000000^201 ≤ 22272364098007^201*2500000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353802543 2500000000 22272364098007 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2098786827/10000000000 : ℝ), (1310795953/2500000000 : ℝ), (1353802543/2500000000 : ℝ)] ![(12766670469117/100000000000000 : ℝ), (42688601328799/100000000000000 : ℝ), (22272364098007/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2098786827/10000000000 : ℝ)|^265 ≤ (12766670469117/100000000000000 : ℝ)^201
        have hw : |(-2098786827/10000000000 : ℝ)|=(2098786827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310795953/2500000000 : ℝ)|^265 ≤ (42688601328799/100000000000000 : ℝ)^201
        have hw : |(1310795953/2500000000 : ℝ)|=(1310795953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353802543/2500000000 : ℝ)|^265 ≤ (22272364098007/50000000000000 : ℝ)^201
        have hw : |(1353802543/2500000000 : ℝ)|=(1353802543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s7_5 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (530566061/1000000000 : ℝ)*x 0 + (-50361537/250000000 : ℝ)*x 1 + (2707604951/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530566061/1000000000 : ℝ)^265 ≤ (43360503899693/100000000000000 : ℝ)^201 := by
    have hnat : (530566061 : ℕ)^265*100000000000000^201 ≤ 43360503899693^201*1000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530566061 1000000000 43360503899693 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (50361537/250000000 : ℝ)^265 ≤ (12094770821133/100000000000000 : ℝ)^201 := by
    have hnat : (50361537 : ℕ)^265*100000000000000^201 ≤ 12094770821133^201*250000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50361537 250000000 12094770821133 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707604951/5000000000 : ℝ)^265 ≤ (2784045329241/6250000000000 : ℝ)^201 := by
    have hnat : (2707604951 : ℕ)^265*6250000000000^201 ≤ 2784045329241^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707604951 5000000000 2784045329241 6250000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530566061/1000000000 : ℝ), (-50361537/250000000 : ℝ), (2707604951/5000000000 : ℝ)] ![(43360503899693/100000000000000 : ℝ), (12094770821133/100000000000000 : ℝ), (2784045329241/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530566061/1000000000 : ℝ)|^265 ≤ (43360503899693/100000000000000 : ℝ)^201
        have hw : |(530566061/1000000000 : ℝ)|=(530566061/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-50361537/250000000 : ℝ)|^265 ≤ (12094770821133/100000000000000 : ℝ)^201
        have hw : |(-50361537/250000000 : ℝ)|=(50361537/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707604951/5000000000 : ℝ)|^265 ≤ (2784045329241/6250000000000 : ℝ)^201
        have hw : |(2707604951/5000000000 : ℝ)|=(2707604951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s7_6 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5305660201/10000000000 : ℝ)*x 0 + (2707605151/5000000000 : ℝ)*x 1 + (-125903843/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305660201/10000000000 : ℝ)^265 ≤ (21680249746423/50000000000000 : ℝ)^201 := by
    have hnat : (5305660201 : ℕ)^265*50000000000000^201 ≤ 21680249746423^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305660201 10000000000 21680249746423 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707605151/5000000000 : ℝ)^265 ≤ (44544729605869/100000000000000 : ℝ)^201 := by
    have hnat : (2707605151 : ℕ)^265*100000000000000^201 ≤ 44544729605869^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707605151 5000000000 44544729605869 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (125903843/625000000 : ℝ)^265 ≤ (12094770884459/100000000000000 : ℝ)^201 := by
    have hnat : (125903843 : ℕ)^265*100000000000000^201 ≤ 12094770884459^201*625000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125903843 625000000 12094770884459 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305660201/10000000000 : ℝ), (2707605151/5000000000 : ℝ), (-125903843/625000000 : ℝ)] ![(21680249746423/50000000000000 : ℝ), (44544729605869/100000000000000 : ℝ), (12094770884459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305660201/10000000000 : ℝ)|^265 ≤ (21680249746423/50000000000000 : ℝ)^201
        have hw : |(5305660201/10000000000 : ℝ)|=(5305660201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707605151/5000000000 : ℝ)|^265 ≤ (44544729605869/100000000000000 : ℝ)^201
        have hw : |(2707605151/5000000000 : ℝ)|=(2707605151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-125903843/625000000 : ℝ)|^265 ≤ (12094770884459/100000000000000 : ℝ)^201
        have hw : |(-125903843/625000000 : ℝ)|=(125903843/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s7_7 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4343124643/10000000000 : ℝ)*x 0 + (4522545921/10000000000 : ℝ)*x 1 + (1042652491/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4343124643/10000000000 : ℝ)^265 ≤ (16651204887389/50000000000000 : ℝ)^201 := by
    have hnat : (4343124643 : ℕ)^265*50000000000000^201 ≤ 16651204887389^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4343124643 10000000000 16651204887389 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4522545921/10000000000 : ℝ)^265 ≤ (702561230251/2000000000000 : ℝ)^201 := by
    have hnat : (4522545921 : ℕ)^265*2000000000000^201 ≤ 702561230251^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4522545921 10000000000 702561230251 2000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1042652491/2500000000 : ℝ)^265 ≤ (7892382174061/25000000000000 : ℝ)^201 := by
    have hnat : (1042652491 : ℕ)^265*25000000000000^201 ≤ 7892382174061^201*2500000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042652491 2500000000 7892382174061 25000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4343124643/10000000000 : ℝ), (4522545921/10000000000 : ℝ), (1042652491/2500000000 : ℝ)] ![(16651204887389/50000000000000 : ℝ), (702561230251/2000000000000 : ℝ), (7892382174061/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4343124643/10000000000 : ℝ)|^265 ≤ (16651204887389/50000000000000 : ℝ)^201
        have hw : |(4343124643/10000000000 : ℝ)|=(4343124643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4522545921/10000000000 : ℝ)|^265 ≤ (702561230251/2000000000000 : ℝ)^201
        have hw : |(4522545921/10000000000 : ℝ)|=(4522545921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1042652491/2500000000 : ℝ)|^265 ≤ (7892382174061/25000000000000 : ℝ)^201
        have hw : |(1042652491/2500000000 : ℝ)|=(1042652491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1280_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152290869/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7333/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2199/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (10997/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1833/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7333/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2199/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7333/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2199/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7333/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2199/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7333/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2199/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7333/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2199/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7333/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2199/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (2199/20000 : ℝ) ^ (4239/1024 : ℝ) ≤ (429482367660837/4000000000000000000 : ℝ) := by
    have hpowers : (2199/20000 : ℝ)^4239 ≤ (429482367660837/4000000000000000000 : ℝ)^1024 := by
      have hnat : (2199 : ℕ)^4239*4000000000000000000^1024 ≤ 429482367660837^1024*20000^4239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2199 20000 429482367660837 4000000000000000000 4239 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2199/20000 : ℝ)) (X := (429482367660837/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7333/50000 : ℝ) ^ (4239/1024 : ℝ) ≤ (7077069280848493/20000000000000000000 : ℝ) := by
    have hpowers : (7333/50000 : ℝ)^4239 ≤ (7077069280848493/20000000000000000000 : ℝ)^1024 := by
      have hnat : (7333 : ℕ)^4239*20000000000000000000^1024 ≤ 7077069280848493^1024*50000^4239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7333 50000 7077069280848493 20000000000000000000 4239 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7333/50000 : ℝ)) (X := (7077069280848493/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000429482367660837/2000000000000000000 : ℝ) ≤ (1000051870032481/1000000000000000 : ℝ) ^ (4239/1024 : ℝ) := by
    have hpowers : (2000429482367660837/2000000000000000000 : ℝ)^1024 ≤ (1000051870032481/1000000000000000 : ℝ)^4239 := by
      have hnat : (2000429482367660837 : ℕ)^1024*1000000000000000^4239 ≤ 1000051870032481^4239*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000429482367660837 2000000000000000000 1000051870032481 1000000000000000 1024 4239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000051870032481/1000000000000000 : ℝ)) (X := (2000429482367660837/2000000000000000000 : ℝ)) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004612240559576339/10000000000000000000 : ℝ) ≤ (5000556983781149/5000000000000000 : ℝ) ^ (4239/1024 : ℝ) := by
    have hpowers : (10004612240559576339/10000000000000000000 : ℝ)^1024 ≤ (5000556983781149/5000000000000000 : ℝ)^4239 := by
      have hnat : (10004612240559576339 : ℕ)^1024*5000000000000000^4239 ≤ 5000556983781149^4239*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004612240559576339 10000000000000000000 5000556983781149 5000000000000000 1024 4239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000556983781149/5000000000000000 : ℝ)) (X := (10004612240559576339/10000000000000000000 : ℝ)) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007077069280848493/10000000000000000000 : ℝ) ≤ (5000854617399893/5000000000000000 : ℝ) ^ (4239/1024 : ℝ) := by
    have hpowers : (10007077069280848493/10000000000000000000 : ℝ)^1024 ≤ (5000854617399893/5000000000000000 : ℝ)^4239 := by
      have hnat : (10007077069280848493 : ℕ)^1024*5000000000000000^4239 ≤ 5000854617399893^4239*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007077069280848493 10000000000000000000 5000854617399893 5000000000000000 1024 4239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000854617399893/5000000000000000 : ℝ)) (X := (10007077069280848493/10000000000000000000 : ℝ)) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(429482367660837/4000000000000000000 : ℝ) ≤ ((3669881422234001639/3671000000000000000 : ℝ)+2*(37204202343/22943750000000 : ℝ)*(2199/20000 : ℝ))^(4239/1024 : ℝ) := by
    rw [show (3669881422234001639/3671000000000000000 : ℝ)+2*(37204202343/22943750000000 : ℝ)*(2199/20000 : ℝ)=(1000051870032481/1000000000000000 : ℝ) by norm_num, show 1+2*(429482367660837/4000000000000000000 : ℝ)=(2000429482367660837/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7077069280848493/20000000000000000000 : ℝ)+(429482367660837/4000000000000000000 : ℝ) ≤ ((3669881422234001639/3671000000000000000 : ℝ)+(37204202343/22943750000000 : ℝ)*((7333/50000 : ℝ)+(2199/20000 : ℝ)))^(4239/1024 : ℝ) := by
    rw [show (3669881422234001639/3671000000000000000 : ℝ)+(37204202343/22943750000000 : ℝ)*((7333/50000 : ℝ)+(2199/20000 : ℝ))=(5000556983781149/5000000000000000 : ℝ) by norm_num, show 1+(7077069280848493/20000000000000000000 : ℝ)+(429482367660837/4000000000000000000 : ℝ)=(10004612240559576339/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7077069280848493/20000000000000000000 : ℝ) ≤ ((3669881422234001639/3671000000000000000 : ℝ)+2*(37204202343/22943750000000 : ℝ)*(7333/50000 : ℝ))^(4239/1024 : ℝ) := by
    rw [show (3669881422234001639/3671000000000000000 : ℝ)+2*(37204202343/22943750000000 : ℝ)*(7333/50000 : ℝ)=(5000854617399893/5000000000000000 : ℝ) by norm_num, show 1+2*(7077069280848493/20000000000000000000 : ℝ)=(10007077069280848493/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3669881422234001639/3671000000000000000 : ℝ)*(X 1 0+X 2 0)+(37204202343/22943750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4239/1024 : ℝ)) (lo := (2199/20000 : ℝ)) (hi := (7333/50000 : ℝ)) (c := (3669881422234001639/3671000000000000000 : ℝ)) (alpha := (37204202343/22943750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3669881422234001639/3671000000000000000 : ℝ)*(X 0 1+X 2 1)+(37204202343/22943750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4239/1024 : ℝ)) (lo := (2199/20000 : ℝ)) (hi := (7333/50000 : ℝ)) (c := (3669881422234001639/3671000000000000000 : ℝ)) (alpha := (37204202343/22943750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3669881422234001639/3671000000000000000 : ℝ)*(X 0 2+X 1 2)+(37204202343/22943750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4239/1024 : ℝ)) (lo := (2199/20000 : ℝ)) (hi := (7333/50000 : ℝ)) (c := (3669881422234001639/3671000000000000000 : ℝ)) (alpha := (37204202343/22943750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1049387249/5000000000 : ℝ)*X 0 0+(5415830121/10000000000 : ℝ)*X 0 1+(1048513329/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668743969/1250000000 : ℝ)*X 1 0+(-1093552499/5000000000 : ℝ)*X 1 1+(1048513427/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069990373/2000000000 : ℝ)*X 2 0+(5242565607/10000000000 : ℝ)*X 2 1+(-2187106867/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4343097113/10000000000 : ℝ)*X 0 0+(1042335627/2500000000 : ℝ)*X 0 1+(2261904081/5000000000 : ℝ)*X 0 2+(4343097113/10000000000 : ℝ)*X 1 0+(1042335627/2500000000 : ℝ)*X 1 1+(2261904081/5000000000 : ℝ)*X 1 2+(4343097113/10000000000 : ℝ)*X 2 0+(1042335627/2500000000 : ℝ)*X 2 1+(2261904081/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2098786827/10000000000 : ℝ)*X 0 0+(1310795953/2500000000 : ℝ)*X 0 1+(1353802543/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530566061/1000000000 : ℝ)*X 1 0+(-50361537/250000000 : ℝ)*X 1 1+(2707604951/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305660201/10000000000 : ℝ)*X 2 0+(2707605151/5000000000 : ℝ)*X 2 1+(-125903843/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4343124643/10000000000 : ℝ)*X 0 0+(4522545921/10000000000 : ℝ)*X 0 1+(1042652491/2500000000 : ℝ)*X 0 2+(4343124643/10000000000 : ℝ)*X 1 0+(4522545921/10000000000 : ℝ)*X 1 1+(1042652491/2500000000 : ℝ)*X 1 2+(4343124643/10000000000 : ℝ)*X 2 0+(4522545921/10000000000 : ℝ)*X 2 1+(1042652491/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (77582964608195435568332847/9177500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (284943093/100000000000000 : ℝ)*(base15) + (308594239/100000000000000 : ℝ)*(upper2) + (1898931/10000000000000 : ℝ)*(upper4) + (102702553/50000000000000 : ℝ)*(lower5) + (214818973475291/5000000000000 : ℝ)*(major0) + (214818973475291/5000000000000 : ℝ)*(major1) + (4296379469505821/100000000000000 : ℝ)*(major2) + (1442896026666683/25000000000000 : ℝ)*(sp0) + (57715915500569/1000000000000 : ℝ)*(sp1) + (360721352471799/6250000000000 : ℝ)*(sp2) + (705289563558971/25000000000000 : ℝ)*(sp3) + (7728333261/100000000000000 : ℝ)*(sp4) + (50195451209/100000000000000 : ℝ)*(sp6) + (2141997227/25000000000000 : ℝ)*(sp7) + (352645852778099/12500000000000 : ℝ)*(f.failure) + (5771591834999993/100000000000000 : ℝ)*(f.sum) + (50012037624589/18355000000000000000000000000 : ℝ)*base65 + (40965115292794051/18355000000000000000000000000000 : ℝ)*base68 + (2627088154103559381/367100000000000000000000000000000 : ℝ)*base70 + (457982358114454051/18355000000000000000000000000000 : ℝ)*base72 + (101854523949/4588750000000000000000000000 : ℝ)*base74 + (150942392493640619/367100000000000000000000000000000 : ℝ)*base75 + (48839161736193051/18355000000000000000000000000000 : ℝ)*base78 + (57457388419251949/18355000000000000000000000000000 : ℝ)*base79 + (285109421971/458875000000000000000000000 : ℝ)*base82 + (10878031/1250000000000000000000 : ℝ)*base89 + (10878031/1250000000000000000000 : ℝ)*base91 + (1621969/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1960535786723700198931744053/183550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (281089047/20000000000000 : ℝ)*(base19) + (341553073/20000000000000 : ℝ)*(base23) + (121853887/25000000000000 : ℝ)*(lower1) + (85186857/25000000000000 : ℝ)*(lower4) + (64729471/100000000000000 : ℝ)*(lower5) + (865444027992059/20000000000000 : ℝ)*(major0) + (865444027992059/20000000000000 : ℝ)*(major1) + (540902517495037/12500000000000 : ℝ)*(major2) + (12960880537/100000000000000 : ℝ)*(sp2) + (2165533067/50000000000000 : ℝ)*(sp3) + (2906510969873039/50000000000000 : ℝ)*(sp4) + (5813020534300843/100000000000000 : ℝ)*(sp5) + (363312954443761/6250000000000 : ℝ)*(sp6) + (710353413267023/25000000000000 : ℝ)*(sp7) + (1420708992067113/50000000000000 : ℝ)*(f.failure) + (2906510969873039/50000000000000 : ℝ)*(f.sum) + (2369348070557/2294375000000000000000000000 : ℝ)*base66 + (1026076465239080701/73420000000000000000000000000000 : ℝ)*base67 + (74414806132915643/45887500000000000000000000000000 : ℝ)*base69 + (2330332813047879299/73420000000000000000000000000000 : ℝ)*base72 + (3003696061879/4588750000000000000000000000 : ℝ)*base74 + (396644082734540643/45887500000000000000000000000000 : ℝ)*base75 + (189884452840724701/73420000000000000000000000000000 : ℝ)*base77 + (723789425983604701/73420000000000000000000000000000 : ℝ)*base79 + (8789000133433/3671000000000000000000000000 : ℝ)*base81 + (4908803/5000000000000000000000 : ℝ)*base90 + (4908803/5000000000000000000000 : ℝ)*base92 + (54908803/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1280_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152290869/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7333/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2199/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10997/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1833/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1280_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1280_s8_0 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5349947791/10000000000 : ℝ)*x 0 + (1310645671/2500000000 : ℝ)*x 1 + (-87483589/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349947791/10000000000 : ℝ)^265 ≤ (21919158674669/50000000000000 : ℝ)^201 := by
    have hnat : (5349947791 : ℕ)^265*50000000000000^201 ≤ 21919158674669^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349947791 10000000000 21919158674669 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310645671/2500000000 : ℝ)^265 ≤ (42682148863329/100000000000000 : ℝ)^201 := by
    have hnat : (1310645671 : ℕ)^265*100000000000000^201 ≤ 42682148863329^201*2500000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310645671 2500000000 42682148863329 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (87483589/400000000 : ℝ)^265 ≤ (13479533767177/100000000000000 : ℝ)^201 := by
    have hnat : (87483589 : ℕ)^265*100000000000000^201 ≤ 13479533767177^201*400000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87483589 400000000 13479533767177 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349947791/10000000000 : ℝ), (1310645671/2500000000 : ℝ), (-87483589/400000000 : ℝ)] ![(21919158674669/50000000000000 : ℝ), (42682148863329/100000000000000 : ℝ), (13479533767177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349947791/10000000000 : ℝ)|^265 ≤ (21919158674669/50000000000000 : ℝ)^201
        have hw : |(5349947791/10000000000 : ℝ)|=(5349947791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310645671/2500000000 : ℝ)|^265 ≤ (42682148863329/100000000000000 : ℝ)^201
        have hw : |(1310645671/2500000000 : ℝ)|=(1310645671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-87483589/400000000 : ℝ)|^265 ≤ (13479533767177/100000000000000 : ℝ)^201
        have hw : |(-87483589/400000000 : ℝ)|=(87483589/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s8_1 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-419757853/2000000000 : ℝ)*x 0 + (1310800007/2500000000 : ℝ)*x 1 + (2707596159/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419757853/2000000000 : ℝ)^265 ≤ (2553338004239/20000000000000 : ℝ)^201 := by
    have hnat : (419757853 : ℕ)^265*20000000000000^201 ≤ 2553338004239^201*2000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419757853 2000000000 2553338004239 20000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310800007/2500000000 : ℝ)^265 ≤ (2134438769673/5000000000000 : ℝ)^201 := by
    have hnat : (1310800007 : ℕ)^265*5000000000000^201 ≤ 2134438769673^201*2500000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310800007 2500000000 2134438769673 5000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707596159/5000000000 : ℝ)^265 ≤ (22272267284463/50000000000000 : ℝ)^201 := by
    have hnat : (2707596159 : ℕ)^265*50000000000000^201 ≤ 22272267284463^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707596159 5000000000 22272267284463 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-419757853/2000000000 : ℝ), (1310800007/2500000000 : ℝ), (2707596159/5000000000 : ℝ)] ![(2553338004239/20000000000000 : ℝ), (2134438769673/5000000000000 : ℝ), (22272267284463/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-419757853/2000000000 : ℝ)|^265 ≤ (2553338004239/20000000000000 : ℝ)^201
        have hw : |(-419757853/2000000000 : ℝ)|=(419757853/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310800007/2500000000 : ℝ)|^265 ≤ (2134438769673/5000000000000 : ℝ)^201
        have hw : |(1310800007/2500000000 : ℝ)|=(1310800007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707596159/5000000000 : ℝ)|^265 ≤ (22272267284463/50000000000000 : ℝ)^201
        have hw : |(2707596159/5000000000 : ℝ)|=(2707596159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s8_2 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2652832307/5000000000 : ℝ)*x 0 + (-1007240061/5000000000 : ℝ)*x 1 + (5415192317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652832307/5000000000 : ℝ)^265 ≤ (8672109408309/20000000000000 : ℝ)^201 := by
    have hnat : (2652832307 : ℕ)^265*20000000000000^201 ≤ 8672109408309^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652832307 5000000000 8672109408309 20000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1007240061/5000000000 : ℝ)^265 ≤ (12094918385547/100000000000000 : ℝ)^201 := by
    have hnat : (1007240061 : ℕ)^265*100000000000000^201 ≤ 12094918385547^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007240061 5000000000 12094918385547 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415192317/10000000000 : ℝ)^265 ≤ (44544534558081/100000000000000 : ℝ)^201 := by
    have hnat : (5415192317 : ℕ)^265*100000000000000^201 ≤ 44544534558081^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415192317 10000000000 44544534558081 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652832307/5000000000 : ℝ), (-1007240061/5000000000 : ℝ), (5415192317/10000000000 : ℝ)] ![(8672109408309/20000000000000 : ℝ), (12094918385547/100000000000000 : ℝ), (44544534558081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652832307/5000000000 : ℝ)|^265 ≤ (8672109408309/20000000000000 : ℝ)^201
        have hw : |(2652832307/5000000000 : ℝ)|=(2652832307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1007240061/5000000000 : ℝ)|^265 ≤ (12094918385547/100000000000000 : ℝ)^201
        have hw : |(-1007240061/5000000000 : ℝ)|=(1007240061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415192317/10000000000 : ℝ)|^265 ≤ (44544534558081/100000000000000 : ℝ)^201
        have hw : |(5415192317/10000000000 : ℝ)|=(5415192317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s8_3 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2652832307/5000000000 : ℝ)*x 0 + (5415192317/10000000000 : ℝ)*x 1 + (-1007240061/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652832307/5000000000 : ℝ)^265 ≤ (8672109408309/20000000000000 : ℝ)^201 := by
    have hnat : (2652832307 : ℕ)^265*20000000000000^201 ≤ 8672109408309^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652832307 5000000000 8672109408309 20000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415192317/10000000000 : ℝ)^265 ≤ (44544534558081/100000000000000 : ℝ)^201 := by
    have hnat : (5415192317 : ℕ)^265*100000000000000^201 ≤ 44544534558081^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415192317 10000000000 44544534558081 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1007240061/5000000000 : ℝ)^265 ≤ (12094918385547/100000000000000 : ℝ)^201 := by
    have hnat : (1007240061 : ℕ)^265*100000000000000^201 ≤ 12094918385547^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007240061 5000000000 12094918385547 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652832307/5000000000 : ℝ), (5415192317/10000000000 : ℝ), (-1007240061/5000000000 : ℝ)] ![(8672109408309/20000000000000 : ℝ), (44544534558081/100000000000000 : ℝ), (12094918385547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652832307/5000000000 : ℝ)|^265 ≤ (8672109408309/20000000000000 : ℝ)^201
        have hw : |(2652832307/5000000000 : ℝ)|=(2652832307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415192317/10000000000 : ℝ)|^265 ≤ (44544534558081/100000000000000 : ℝ)^201
        have hw : |(5415192317/10000000000 : ℝ)|=(5415192317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1007240061/5000000000 : ℝ)|^265 ≤ (12094918385547/100000000000000 : ℝ)^201
        have hw : |(-1007240061/5000000000 : ℝ)|=(1007240061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s8_4 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1085781571/2500000000 : ℝ)*x 0 + (4522509989/10000000000 : ℝ)*x 1 + (4170645173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1085781571/2500000000 : ℝ)^265 ≤ (33302426364221/100000000000000 : ℝ)^201 := by
    have hnat : (1085781571 : ℕ)^265*100000000000000^201 ≤ 33302426364221^201*2500000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085781571 2500000000 33302426364221 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4522509989/10000000000 : ℝ)^265 ≤ (17563846775747/50000000000000 : ℝ)^201 := by
    have hnat : (4522509989 : ℕ)^265*50000000000000^201 ≤ 17563846775747^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4522509989 10000000000 17563846775747 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4170645173/10000000000 : ℝ)^265 ≤ (31569880072663/100000000000000 : ℝ)^201 := by
    have hnat : (4170645173 : ℕ)^265*100000000000000^201 ≤ 31569880072663^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170645173 10000000000 31569880072663 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1085781571/2500000000 : ℝ), (4522509989/10000000000 : ℝ), (4170645173/10000000000 : ℝ)] ![(33302426364221/100000000000000 : ℝ), (17563846775747/50000000000000 : ℝ), (31569880072663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1085781571/2500000000 : ℝ)|^265 ≤ (33302426364221/100000000000000 : ℝ)^201
        have hw : |(1085781571/2500000000 : ℝ)|=(1085781571/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4522509989/10000000000 : ℝ)|^265 ≤ (17563846775747/50000000000000 : ℝ)^201
        have hw : |(4522509989/10000000000 : ℝ)|=(4522509989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4170645173/10000000000 : ℝ)|^265 ≤ (31569880072663/100000000000000 : ℝ)^201
        have hw : |(4170645173/10000000000 : ℝ)|=(4170645173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1280_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152290869/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1833/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10997/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10997/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14663/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1833/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10997/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1833/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10997/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1833/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10997/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1833/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10997/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1833/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10997/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1833/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10997/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10997/100000 : ℝ) ^ (4239/1024 : ℝ) ≤ (214902931330499/2000000000000000000 : ℝ) := by
    have hpowers : (10997/100000 : ℝ)^4239 ≤ (214902931330499/2000000000000000000 : ℝ)^1024 := by
      have hnat : (10997 : ℕ)^4239*2000000000000000000^1024 ≤ 214902931330499^1024*100000^4239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10997 100000 214902931330499 2000000000000000000 4239 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10997/100000 : ℝ)) (X := (214902931330499/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1833/12500 : ℝ) ^ (4239/1024 : ℝ) ≤ (35365374832112031/100000000000000000000 : ℝ) := by
    have hpowers : (1833/12500 : ℝ)^4239 ≤ (35365374832112031/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1833 : ℕ)^4239*100000000000000000000^1024 ≤ 35365374832112031^1024*12500^4239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1833 12500 35365374832112031 100000000000000000000 4239 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1833/12500 : ℝ)) (X := (35365374832112031/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000214902931330499/1000000000000000000 : ℝ) ≤ (5000259545494393/5000000000000000 : ℝ) ^ (4239/1024 : ℝ) := by
    have hpowers : (1000214902931330499/1000000000000000000 : ℝ)^1024 ≤ (5000259545494393/5000000000000000 : ℝ)^4239 := by
      have hnat : (1000214902931330499 : ℕ)^1024*5000000000000000^4239 ≤ 5000259545494393^4239*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000214902931330499 1000000000000000000 5000259545494393 5000000000000000 1024 4239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000259545494393/5000000000000000 : ℝ)) (X := (1000214902931330499/1000000000000000000 : ℝ)) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046110521398636981/100000000000000000000 : ℝ) ≤ (2500278420145097/2500000000000000 : ℝ) ^ (4239/1024 : ℝ) := by
    have hpowers : (100046110521398636981/100000000000000000000 : ℝ)^1024 ≤ (2500278420145097/2500000000000000 : ℝ)^4239 := by
      have hnat : (100046110521398636981 : ℕ)^1024*2500000000000000^4239 ≤ 2500278420145097^4239*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046110521398636981 100000000000000000000 2500278420145097 2500000000000000 1024 4239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500278420145097/2500000000000000 : ℝ)) (X := (100046110521398636981/100000000000000000000 : ℝ)) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035365374832112031/50000000000000000000 : ℝ) ≤ (1000170827017199/1000000000000000 : ℝ) ^ (4239/1024 : ℝ) := by
    have hpowers : (50035365374832112031/50000000000000000000 : ℝ)^1024 ≤ (1000170827017199/1000000000000000 : ℝ)^4239 := by
      have hnat : (50035365374832112031 : ℕ)^1024*1000000000000000^4239 ≤ 1000170827017199^4239*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035365374832112031 50000000000000000000 1000170827017199 1000000000000000 1024 4239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000170827017199/1000000000000000 : ℝ)) (X := (50035365374832112031/50000000000000000000 : ℝ)) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(214902931330499/2000000000000000000 : ℝ) ≤ ((18329413051589091937/18335000000000000000 : ℝ)+2*(297294795801/183350000000000 : ℝ)*(10997/100000 : ℝ))^(4239/1024 : ℝ) := by
    rw [show (18329413051589091937/18335000000000000000 : ℝ)+2*(297294795801/183350000000000 : ℝ)*(10997/100000 : ℝ)=(5000259545494393/5000000000000000 : ℝ) by norm_num, show 1+2*(214902931330499/2000000000000000000 : ℝ)=(1000214902931330499/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35365374832112031/100000000000000000000 : ℝ)+(214902931330499/2000000000000000000 : ℝ) ≤ ((18329413051589091937/18335000000000000000 : ℝ)+(297294795801/183350000000000 : ℝ)*((1833/12500 : ℝ)+(10997/100000 : ℝ)))^(4239/1024 : ℝ) := by
    rw [show (18329413051589091937/18335000000000000000 : ℝ)+(297294795801/183350000000000 : ℝ)*((1833/12500 : ℝ)+(10997/100000 : ℝ))=(2500278420145097/2500000000000000 : ℝ) by norm_num, show 1+(35365374832112031/100000000000000000000 : ℝ)+(214902931330499/2000000000000000000 : ℝ)=(100046110521398636981/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35365374832112031/100000000000000000000 : ℝ) ≤ ((18329413051589091937/18335000000000000000 : ℝ)+2*(297294795801/183350000000000 : ℝ)*(1833/12500 : ℝ))^(4239/1024 : ℝ) := by
    rw [show (18329413051589091937/18335000000000000000 : ℝ)+2*(297294795801/183350000000000 : ℝ)*(1833/12500 : ℝ)=(1000170827017199/1000000000000000 : ℝ) by norm_num, show 1+2*(35365374832112031/100000000000000000000 : ℝ)=(50035365374832112031/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18329413051589091937/18335000000000000000 : ℝ)*(X 1 0+X 2 0)+(297294795801/183350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4239/1024 : ℝ)) (lo := (10997/100000 : ℝ)) (hi := (1833/12500 : ℝ)) (c := (18329413051589091937/18335000000000000000 : ℝ)) (alpha := (297294795801/183350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18329413051589091937/18335000000000000000 : ℝ)*(X 0 1+X 2 1)+(297294795801/183350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4239/1024 : ℝ)) (lo := (10997/100000 : ℝ)) (hi := (1833/12500 : ℝ)) (c := (18329413051589091937/18335000000000000000 : ℝ)) (alpha := (297294795801/183350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18329413051589091937/18335000000000000000 : ℝ)*(X 0 2+X 1 2)+(297294795801/183350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4239/1024 : ℝ)) (lo := (10997/100000 : ℝ)) (hi := (1833/12500 : ℝ)) (c := (18329413051589091937/18335000000000000000 : ℝ)) (alpha := (297294795801/183350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5349947791/10000000000 : ℝ)*X 2 0+(1310645671/2500000000 : ℝ)*X 2 1+(-87483589/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s8_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-419757853/2000000000 : ℝ)*X 0 0+(1310800007/2500000000 : ℝ)*X 0 1+(2707596159/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s8_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2652832307/5000000000 : ℝ)*X 1 0+(-1007240061/5000000000 : ℝ)*X 1 1+(5415192317/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s8_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2652832307/5000000000 : ℝ)*X 2 0+(5415192317/10000000000 : ℝ)*X 2 1+(-1007240061/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s8_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((1085781571/2500000000 : ℝ)*X 0 0+(4522509989/10000000000 : ℝ)*X 0 1+(4170645173/10000000000 : ℝ)*X 0 2+(1085781571/2500000000 : ℝ)*X 1 0+(4522509989/10000000000 : ℝ)*X 1 1+(4170645173/10000000000 : ℝ)*X 1 2+(1085781571/2500000000 : ℝ)*X 2 0+(4522509989/10000000000 : ℝ)*X 2 1+(4170645173/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s8_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (172077037131233748758949333/45837500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (167798453/25000000000000 : ℝ)*(base19) + (145919561/20000000000000 : ℝ)*(base23) + (57721179/25000000000000 : ℝ)*(lower1) + (38131659/50000000000000 : ℝ)*(upper3) + (6623113/25000000000000 : ℝ)*(lower4) + (38476943/50000000000000 : ℝ)*(upper5) + (432809706010403/10000000000000 : ℝ)*(major0) + (432809706010403/10000000000000 : ℝ)*(major1) + (432809706010403/10000000000000 : ℝ)*(major2) + (1015001337/100000000000000 : ℝ)*(sp0) + (1162840038337123/20000000000000 : ℝ)*(sp1) + (5814199520491803/100000000000000 : ℝ)*(sp2) + (5814198447086473/100000000000000 : ℝ)*(sp3) + (138769228681/4882812500 : ℝ)*(sp4) + (138769228681/4882812500 : ℝ)*(f.failure) + (1162840038337123/20000000000000 : ℝ)*(f.sum) + (9759557204103/3667000000000000000000000000 : ℝ)*base66 + (291507847733279389/183350000000000000000000000000000 : ℝ)*base68 + (974503882137779389/183350000000000000000000000000000 : ℝ)*base70 + (306841782043020611/183350000000000000000000000000000 : ℝ)*base71 + (9082661897453/1833500000000000000000000000 : ℝ)*base74 + (2046729544854129389/183350000000000000000000000000000 : ℝ)*base76 + (588860361639429389/183350000000000000000000000000000 : ℝ)*base78 + (526577074370429389/183350000000000000000000000000000 : ℝ)*base80 + (19675665221191/3667000000000000000000000000 : ℝ)*base82 + (38437/3906250000000000000 : ℝ)*base89 + (38437/3906250000000000000 : ℝ)*base91 + (38437/3906250000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1280_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152290869/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1833/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10997/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10997/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14663/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1280_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1280_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152290869/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14679/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5491/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10997/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14663/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1280_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1280_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1280_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152290869/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14679/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5491/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10997/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14663/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1280_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

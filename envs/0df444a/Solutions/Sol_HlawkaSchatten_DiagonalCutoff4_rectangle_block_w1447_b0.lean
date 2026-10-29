-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1447_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:58:16.838977+00:00
-- url     : https://prove2.me/submissions/19ebfe37-11ae-437a-b4e6-ac0810cbdb2a

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
theorem support_rectangle_w1447_s0_0 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1748667203/10000000000 : ℝ)*x 0 + (5952788363/10000000000 : ℝ)*x 1 + (4835336733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1748667203/10000000000 : ℝ)^4407 ≤ (10315309353171/100000000000000 : ℝ)^3383 := by
    have hnat : (1748667203 : ℕ)^4407*100000000000000^3383 ≤ 10315309353171^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1748667203 10000000000 10315309353171 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5952788363/10000000000 : ℝ)^4407 ≤ (10175613127609/20000000000000 : ℝ)^3383 := by
    have hnat : (5952788363 : ℕ)^4407*20000000000000^3383 ≤ 10175613127609^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5952788363 10000000000 10175613127609 20000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4835336733/10000000000 : ℝ)^4407 ≤ (2425414062639/6250000000000 : ℝ)^3383 := by
    have hnat : (4835336733 : ℕ)^4407*6250000000000^3383 ≤ 2425414062639^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4835336733 10000000000 2425414062639 6250000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1748667203/10000000000 : ℝ), (5952788363/10000000000 : ℝ), (4835336733/10000000000 : ℝ)] ![(10315309353171/100000000000000 : ℝ), (10175613127609/20000000000000 : ℝ), (2425414062639/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1748667203/10000000000 : ℝ)|^4407 ≤ (10315309353171/100000000000000 : ℝ)^3383
        have hw : |(-1748667203/10000000000 : ℝ)|=(1748667203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5952788363/10000000000 : ℝ)|^4407 ≤ (10175613127609/20000000000000 : ℝ)^3383
        have hw : |(5952788363/10000000000 : ℝ)|=(5952788363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4835336733/10000000000 : ℝ)|^4407 ≤ (2425414062639/6250000000000 : ℝ)^3383
        have hw : |(4835336733/10000000000 : ℝ)|=(4835336733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s0_1 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (274504983/500000000 : ℝ)*x 0 + (-2379129119/10000000000 : ℝ)*x 1 + (2417668299/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (274504983/500000000 : ℝ)^4407 ≤ (45788222883083/100000000000000 : ℝ)^3383 := by
    have hnat : (274504983 : ℕ)^4407*100000000000000^3383 ≤ 45788222883083^3383*500000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274504983 500000000 45788222883083 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2379129119/10000000000 : ℝ)^4407 ≤ (7702576757283/50000000000000 : ℝ)^3383 := by
    have hnat : (2379129119 : ℕ)^4407*50000000000000^3383 ≤ 7702576757283^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2379129119 10000000000 7702576757283 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2417668299/5000000000 : ℝ)^4407 ≤ (9701655897703/25000000000000 : ℝ)^3383 := by
    have hnat : (2417668299 : ℕ)^4407*25000000000000^3383 ≤ 9701655897703^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2417668299 5000000000 9701655897703 25000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(274504983/500000000 : ℝ), (-2379129119/10000000000 : ℝ), (2417668299/5000000000 : ℝ)] ![(45788222883083/100000000000000 : ℝ), (7702576757283/50000000000000 : ℝ), (9701655897703/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(274504983/500000000 : ℝ)|^4407 ≤ (45788222883083/100000000000000 : ℝ)^3383
        have hw : |(274504983/500000000 : ℝ)|=(274504983/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2379129119/10000000000 : ℝ)|^4407 ≤ (7702576757283/50000000000000 : ℝ)^3383
        have hw : |(-2379129119/10000000000 : ℝ)|=(2379129119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2417668299/5000000000 : ℝ)|^4407 ≤ (9701655897703/25000000000000 : ℝ)^3383
        have hw : |(2417668299/5000000000 : ℝ)|=(2417668299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s0_2 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (274504977/500000000 : ℝ)*x 0 + (2417668279/5000000000 : ℝ)*x 1 + (-1189564661/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (274504977/500000000 : ℝ)^4407 ≤ (715440962177/1562500000000 : ℝ)^3383 := by
    have hnat : (274504977 : ℕ)^4407*1562500000000^3383 ≤ 715440962177^3383*500000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274504977 500000000 715440962177 1562500000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2417668279/5000000000 : ℝ)^4407 ≤ (4850827896577/12500000000000 : ℝ)^3383 := by
    have hnat : (2417668279 : ℕ)^4407*12500000000000^3383 ≤ 4850827896577^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2417668279 5000000000 4850827896577 12500000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1189564661/5000000000 : ℝ)^4407 ≤ (7702577613443/50000000000000 : ℝ)^3383 := by
    have hnat : (1189564661 : ℕ)^4407*50000000000000^3383 ≤ 7702577613443^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1189564661 5000000000 7702577613443 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(274504977/500000000 : ℝ), (2417668279/5000000000 : ℝ), (-1189564661/5000000000 : ℝ)] ![(715440962177/1562500000000 : ℝ), (4850827896577/12500000000000 : ℝ), (7702577613443/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(274504977/500000000 : ℝ)|^4407 ≤ (715440962177/1562500000000 : ℝ)^3383
        have hw : |(274504977/500000000 : ℝ)|=(274504977/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2417668279/5000000000 : ℝ)|^4407 ≤ (4850827896577/12500000000000 : ℝ)^3383
        have hw : |(2417668279/5000000000 : ℝ)|=(2417668279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1189564661/5000000000 : ℝ)|^4407 ≤ (7702577613443/50000000000000 : ℝ)^3383
        have hw : |(-1189564661/5000000000 : ℝ)|=(1189564661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s0_3 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2081715211/5000000000 : ℝ)*x 0 + (3102955827/10000000000 : ℝ)*x 1 + (553632983/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2081715211/5000000000 : ℝ)^4407 ≤ (31934716056153/100000000000000 : ℝ)^3383 := by
    have hnat : (2081715211 : ℕ)^4407*100000000000000^3383 ≤ 31934716056153^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081715211 5000000000 31934716056153 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3102955827/10000000000 : ℝ)^4407 ≤ (10887074436949/50000000000000 : ℝ)^3383 := by
    have hnat : (3102955827 : ℕ)^4407*50000000000000^3383 ≤ 10887074436949^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3102955827 10000000000 10887074436949 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (553632983/1000000000 : ℝ)^4407 ≤ (46291135055273/100000000000000 : ℝ)^3383 := by
    have hnat : (553632983 : ℕ)^4407*100000000000000^3383 ≤ 46291135055273^3383*1000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553632983 1000000000 46291135055273 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2081715211/5000000000 : ℝ), (3102955827/10000000000 : ℝ), (553632983/1000000000 : ℝ)] ![(31934716056153/100000000000000 : ℝ), (10887074436949/50000000000000 : ℝ), (46291135055273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2081715211/5000000000 : ℝ)|^4407 ≤ (31934716056153/100000000000000 : ℝ)^3383
        have hw : |(2081715211/5000000000 : ℝ)|=(2081715211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3102955827/10000000000 : ℝ)|^4407 ≤ (10887074436949/50000000000000 : ℝ)^3383
        have hw : |(3102955827/10000000000 : ℝ)|=(3102955827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(553632983/1000000000 : ℝ)|^4407 ≤ (46291135055273/100000000000000 : ℝ)^3383
        have hw : |(553632983/1000000000 : ℝ)|=(553632983/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s0_4 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1752599223/10000000000 : ℝ)*x 0 + (4863887227/10000000000 : ℝ)*x 1 + (1480804579/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1752599223/10000000000 : ℝ)^4407 ≤ (10345535275089/100000000000000 : ℝ)^3383 := by
    have hnat : (1752599223 : ℕ)^4407*100000000000000^3383 ≤ 10345535275089^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1752599223 10000000000 10345535275089 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4863887227/10000000000 : ℝ)^4407 ≤ (611021627451/1562500000000 : ℝ)^3383 := by
    have hnat : (4863887227 : ℕ)^4407*1562500000000^3383 ≤ 611021627451^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4863887227 10000000000 611021627451 1562500000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1480804579/2500000000 : ℝ)^4407 ≤ (252745402743/500000000000 : ℝ)^3383 := by
    have hnat : (1480804579 : ℕ)^4407*500000000000^3383 ≤ 252745402743^3383*2500000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1480804579 2500000000 252745402743 500000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1752599223/10000000000 : ℝ), (4863887227/10000000000 : ℝ), (1480804579/2500000000 : ℝ)] ![(10345535275089/100000000000000 : ℝ), (611021627451/1562500000000 : ℝ), (252745402743/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1752599223/10000000000 : ℝ)|^4407 ≤ (10345535275089/100000000000000 : ℝ)^3383
        have hw : |(-1752599223/10000000000 : ℝ)|=(1752599223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4863887227/10000000000 : ℝ)|^4407 ≤ (611021627451/1562500000000 : ℝ)^3383
        have hw : |(4863887227/10000000000 : ℝ)|=(4863887227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1480804579/2500000000 : ℝ)|^4407 ≤ (252745402743/500000000000 : ℝ)^3383
        have hw : |(1480804579/2500000000 : ℝ)|=(1480804579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s0_5 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5185024323/10000000000 : ℝ)*x 0 + (-1291247583/10000000000 : ℝ)*x 1 + (1184643677/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5185024323/10000000000 : ℝ)^4407 ≤ (42501938626119/100000000000000 : ℝ)^3383 := by
    have hnat : (5185024323 : ℕ)^4407*100000000000000^3383 ≤ 42501938626119^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185024323 10000000000 42501938626119 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1291247583/10000000000 : ℝ)^4407 ≤ (6948980046671/100000000000000 : ℝ)^3383 := by
    have hnat : (1291247583 : ℕ)^4407*100000000000000^3383 ≤ 6948980046671^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1291247583 10000000000 6948980046671 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1184643677/2000000000 : ℝ)^4407 ≤ (50549081315689/100000000000000 : ℝ)^3383 := by
    have hnat : (1184643677 : ℕ)^4407*100000000000000^3383 ≤ 50549081315689^3383*2000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1184643677 2000000000 50549081315689 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5185024323/10000000000 : ℝ), (-1291247583/10000000000 : ℝ), (1184643677/2000000000 : ℝ)] ![(42501938626119/100000000000000 : ℝ), (6948980046671/100000000000000 : ℝ), (50549081315689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5185024323/10000000000 : ℝ)|^4407 ≤ (42501938626119/100000000000000 : ℝ)^3383
        have hw : |(5185024323/10000000000 : ℝ)|=(5185024323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1291247583/10000000000 : ℝ)|^4407 ≤ (6948980046671/100000000000000 : ℝ)^3383
        have hw : |(-1291247583/10000000000 : ℝ)|=(1291247583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1184643677/2000000000 : ℝ)|^4407 ≤ (50549081315689/100000000000000 : ℝ)^3383
        have hw : |(1184643677/2000000000 : ℝ)|=(1184643677/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s0_6 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (162032011/312500000 : ℝ)*x 0 + (592321823/1000000000 : ℝ)*x 1 + (-1291247783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (162032011/312500000 : ℝ)^4407 ≤ (42501938935787/100000000000000 : ℝ)^3383 := by
    have hnat : (162032011 : ℕ)^4407*100000000000000^3383 ≤ 42501938935787^3383*312500000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162032011 312500000 42501938935787 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (592321823/1000000000 : ℝ)^4407 ≤ (25274539796259/50000000000000 : ℝ)^3383 := by
    have hnat : (592321823 : ℕ)^4407*50000000000000^3383 ≤ 25274539796259^3383*1000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      592321823 1000000000 25274539796259 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1291247783/10000000000 : ℝ)^4407 ≤ (6948981448783/100000000000000 : ℝ)^3383 := by
    have hnat : (1291247783 : ℕ)^4407*100000000000000^3383 ≤ 6948981448783^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1291247783 10000000000 6948981448783 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(162032011/312500000 : ℝ), (592321823/1000000000 : ℝ), (-1291247783/10000000000 : ℝ)] ![(42501938935787/100000000000000 : ℝ), (25274539796259/50000000000000 : ℝ), (6948981448783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(162032011/312500000 : ℝ)|^4407 ≤ (42501938935787/100000000000000 : ℝ)^3383
        have hw : |(162032011/312500000 : ℝ)|=(162032011/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(592321823/1000000000 : ℝ)|^4407 ≤ (25274539796259/50000000000000 : ℝ)^3383
        have hw : |(592321823/1000000000 : ℝ)|=(592321823/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1291247783/10000000000 : ℝ)|^4407 ≤ (6948981448783/100000000000000 : ℝ)^3383
        have hw : |(-1291247783/10000000000 : ℝ)|=(1291247783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s0_7 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2085995977/5000000000 : ℝ)*x 0 + (273707879/500000000 : ℝ)*x 1 + (3167348099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2085995977/5000000000 : ℝ)^4407 ≤ (32020289569021/100000000000000 : ℝ)^3383 := by
    have hnat : (2085995977 : ℕ)^4407*100000000000000^3383 ≤ 32020289569021^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085995977 5000000000 32020289569021 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273707879/500000000 : ℝ)^4407 ≤ (5701886797949/12500000000000 : ℝ)^3383 := by
    have hnat : (273707879 : ℕ)^4407*12500000000000^3383 ≤ 5701886797949^3383*500000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273707879 500000000 5701886797949 12500000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3167348099/10000000000 : ℝ)^4407 ≤ (4472923205857/20000000000000 : ℝ)^3383 := by
    have hnat : (3167348099 : ℕ)^4407*20000000000000^3383 ≤ 4472923205857^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3167348099 10000000000 4472923205857 20000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2085995977/5000000000 : ℝ), (273707879/500000000 : ℝ), (3167348099/10000000000 : ℝ)] ![(32020289569021/100000000000000 : ℝ), (5701886797949/12500000000000 : ℝ), (4472923205857/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2085995977/5000000000 : ℝ)|^4407 ≤ (32020289569021/100000000000000 : ℝ)^3383
        have hw : |(2085995977/5000000000 : ℝ)|=(2085995977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(273707879/500000000 : ℝ)|^4407 ≤ (5701886797949/12500000000000 : ℝ)^3383
        have hw : |(273707879/500000000 : ℝ)|=(273707879/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3167348099/10000000000 : ℝ)|^4407 ≤ (4472923205857/20000000000000 : ℝ)^3383
        have hw : |(3167348099/10000000000 : ℝ)|=(3167348099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1447_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31776097/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1087/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13067/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (2203/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2203 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2203*1^512 ≤ 0^512*1^2203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2203 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2203/512 : ℝ) ≤ (1939857576993169269/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2203 ≤ (1939857576993169269/100000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2203*100000000000000000000^512 ≤ 1939857576993169269^512*5^2203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1939857576993169269 100000000000000000000 2203 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1939857576993169269/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2203/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2203 := by
      have hnat : (1 : ℕ)^512*1^2203 ≤ 1^2203*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (101939857576993169269/100000000000000000000 : ℝ) ≤ (2511188106878789/2500000000000000 : ℝ) ^ (2203/512 : ℝ) := by
    have hpowers : (101939857576993169269/100000000000000000000 : ℝ)^512 ≤ (2511188106878789/2500000000000000 : ℝ)^2203 := by
      have hnat : (101939857576993169269 : ℕ)^512*2500000000000000^2203 ≤ 2511188106878789^2203*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101939857576993169269 100000000000000000000 2511188106878789 2500000000000000 512 2203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2511188106878789/2500000000000000 : ℝ)) (X := (101939857576993169269/100000000000000000000 : ℝ)) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (51939857576993169269/50000000000000000000 : ℝ) ≤ (1261188106878789/1250000000000000 : ℝ) ^ (2203/512 : ℝ) := by
    have hpowers : (51939857576993169269/50000000000000000000 : ℝ)^512 ≤ (1261188106878789/1250000000000000 : ℝ)^2203 := by
      have hnat : (51939857576993169269 : ℕ)^512*1250000000000000^2203 ≤ 1261188106878789^2203*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51939857576993169269 50000000000000000000 1261188106878789 1250000000000000 512 2203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1261188106878789/1250000000000000 : ℝ)) (X := (51939857576993169269/50000000000000000000 : ℝ)) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(11188106878789/1000000000000000 : ℝ)*(0 : ℝ))^(2203/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(11188106878789/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1939857576993169269/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(11188106878789/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2203/512 : ℝ) := by
    rw [show (1 : ℝ)+(11188106878789/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2511188106878789/2500000000000000 : ℝ) by norm_num, show 1+(1939857576993169269/100000000000000000000 : ℝ)+(0 : ℝ)=(101939857576993169269/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1939857576993169269/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(11188106878789/1000000000000000 : ℝ)*(2/5 : ℝ))^(2203/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(11188106878789/1000000000000000 : ℝ)*(2/5 : ℝ)=(1261188106878789/1250000000000000 : ℝ) by norm_num, show 1+2*(1939857576993169269/100000000000000000000 : ℝ)=(51939857576993169269/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(11188106878789/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2203/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11188106878789/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(11188106878789/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2203/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11188106878789/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(11188106878789/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2203/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11188106878789/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1748667203/10000000000 : ℝ)*X 0 0+(5952788363/10000000000 : ℝ)*X 0 1+(4835336733/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((274504983/500000000 : ℝ)*X 1 0+(-2379129119/10000000000 : ℝ)*X 1 1+(2417668299/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((274504977/500000000 : ℝ)*X 2 0+(2417668279/5000000000 : ℝ)*X 2 1+(-1189564661/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2081715211/5000000000 : ℝ)*X 0 0+(3102955827/10000000000 : ℝ)*X 0 1+(553632983/1000000000 : ℝ)*X 0 2+(2081715211/5000000000 : ℝ)*X 1 0+(3102955827/10000000000 : ℝ)*X 1 1+(553632983/1000000000 : ℝ)*X 1 2+(2081715211/5000000000 : ℝ)*X 2 0+(3102955827/10000000000 : ℝ)*X 2 1+(553632983/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1752599223/10000000000 : ℝ)*X 0 0+(4863887227/10000000000 : ℝ)*X 0 1+(1480804579/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5185024323/10000000000 : ℝ)*X 1 0+(-1291247583/10000000000 : ℝ)*X 1 1+(1184643677/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((162032011/312500000 : ℝ)*X 2 0+(592321823/1000000000 : ℝ)*X 2 1+(-1291247783/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2085995977/5000000000 : ℝ)*X 0 0+(273707879/500000000 : ℝ)*X 0 1+(3167348099/10000000000 : ℝ)*X 0 2+(2085995977/5000000000 : ℝ)*X 1 0+(273707879/500000000 : ℝ)*X 1 1+(3167348099/10000000000 : ℝ)*X 1 2+(2085995977/5000000000 : ℝ)*X 2 0+(273707879/500000000 : ℝ)*X 2 1+(3167348099/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4746730157869912977/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17948427/12500000000000 : ℝ)*(base1) + (107109569/10000000000000 : ℝ)*(base19) + (1051535423/100000000000000 : ℝ)*(base23) + (142079571/100000000000000 : ℝ)*(upper3) + (40621543/50000000000000 : ℝ)*(upper5) + (326463672264273/50000000000000 : ℝ)*(major0) + (326463672264273/50000000000000 : ℝ)*(major1) + (326463672264273/50000000000000 : ℝ)*(major2) + (894896614894667/100000000000000 : ℝ)*(sp0) + (894898429905331/100000000000000 : ℝ)*(sp1) + (447449224732799/50000000000000 : ℝ)*(sp2) + (82190668536897/20000000000000 : ℝ)*(sp3) + (302969377/10000000000000 : ℝ)*(sp4) + (385889957/25000000000000 : ℝ)*(sp7) + (410955029831729/100000000000000 : ℝ)*(f.failure) + (894899501001021/100000000000000 : ℝ)*(f.sum) + (25017100569603/25000000000000000000000000000 : ℝ)*base66 + (119366426094603/50000000000000000000000000000 : ℝ)*base68 + (225509948555397/50000000000000000000000000000 : ℝ)*base69 + (106156684105397/50000000000000000000000000000 : ℝ)*base71 + (114265287444603/25000000000000000000000000000 : ℝ)*base74 + (77170536794603/50000000000000000000000000000 : ℝ)*base76 + (42639811105397/50000000000000000000000000000 : ℝ)*base77 + (92638785255397/50000000000000000000000000000 : ℝ)*base79 + (28917637055397/25000000000000000000000000000 : ℝ)*base81 + (5618287/2000000000000000000000 : ℝ)*base90 + (5618287/2000000000000000000000 : ℝ)*base92 + (5618287/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (117835929026080327598529/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33841739/6250000000000 : ℝ)*(base19) + (17068347/3125000000000 : ℝ)*(base23) + (8665387/10000000000000 : ℝ)*(base32) + (21450241/25000000000000 : ℝ)*(upper3) + (470307/1250000000000 : ℝ)*(upper5) + (688745340926113/100000000000000 : ℝ)*(major0) + (688745340926113/100000000000000 : ℝ)*(major1) + (688745340926113/100000000000000 : ℝ)*(major2) + (650149617/50000000000000 : ℝ)*(sp1) + (1290773831/100000000000000 : ℝ)*(sp2) + (943991586139927/100000000000000 : ℝ)*(sp4) + (943989744372869/100000000000000 : ℝ)*(sp5) + (58999359323687/6250000000000 : ℝ)*(sp6) + (21674946525057/5000000000000 : ℝ)*(sp7) + (43349901715501/10000000000000 : ℝ)*(f.failure) + (943991586139927/100000000000000 : ℝ)*(f.sum) + (62098446032843/50000000000000000000000000000 : ℝ)*base66 + (929853733017157/100000000000000000000000000000 : ℝ)*base67 + (304344483282843/100000000000000000000000000000 : ℝ)*base70 + (130241027217157/100000000000000000000000000000 : ℝ)*base71 + (181828059567157/50000000000000000000000000000 : ℝ)*base73 + (183429560217157/100000000000000000000000000000 : ℝ)*base75 + (58641247517157/100000000000000000000000000000 : ℝ)*base77 + (437711190117157/100000000000000000000000000000 : ℝ)*base79 + (180370181182843/50000000000000000000000000000 : ℝ)*base82 + (179597/200000000000000000000 : ℝ)*base89 + (179597/200000000000000000000 : ℝ)*base91 + (179597/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1447_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31776097/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1087/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13067/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1447_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1447_s1_0 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-383696269/2000000000 : ℝ)*x 0 + (5598089883/10000000000 : ℝ)*x 1 + (5081139849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (383696269/2000000000 : ℝ)^4407 ≤ (2909752677573/25000000000000 : ℝ)^3383 := by
    have hnat : (383696269 : ℕ)^4407*25000000000000^3383 ≤ 2909752677573^3383*2000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      383696269 2000000000 2909752677573 25000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5598089883/10000000000 : ℝ)^4407 ≤ (9392994551217/20000000000000 : ℝ)^3383 := by
    have hnat : (5598089883 : ℕ)^4407*20000000000000^3383 ≤ 9392994551217^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5598089883 10000000000 9392994551217 20000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5081139849/10000000000 : ℝ)^4407 ≤ (41396016526203/100000000000000 : ℝ)^3383 := by
    have hnat : (5081139849 : ℕ)^4407*100000000000000^3383 ≤ 41396016526203^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5081139849 10000000000 41396016526203 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-383696269/2000000000 : ℝ), (5598089883/10000000000 : ℝ), (5081139849/10000000000 : ℝ)] ![(2909752677573/25000000000000 : ℝ), (9392994551217/20000000000000 : ℝ), (41396016526203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-383696269/2000000000 : ℝ)|^4407 ≤ (2909752677573/25000000000000 : ℝ)^3383
        have hw : |(-383696269/2000000000 : ℝ)|=(383696269/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5598089883/10000000000 : ℝ)|^4407 ≤ (9392994551217/20000000000000 : ℝ)^3383
        have hw : |(5598089883/10000000000 : ℝ)|=(5598089883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5081139849/10000000000 : ℝ)|^4407 ≤ (41396016526203/100000000000000 : ℝ)^3383
        have hw : |(5081139849/10000000000 : ℝ)|=(5081139849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s1_1 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5395010431/10000000000 : ℝ)*x 0 + (-17536289/80000000 : ℝ)*x 1 + (508114009/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5395010431/10000000000 : ℝ)^4407 ≤ (44757833458523/100000000000000 : ℝ)^3383 := by
    have hnat : (5395010431 : ℕ)^4407*100000000000000^3383 ≤ 44757833458523^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395010431 10000000000 44757833458523 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17536289/80000000 : ℝ)^4407 ≤ (13846147449483/100000000000000 : ℝ)^3383 := by
    have hnat : (17536289 : ℕ)^4407*100000000000000^3383 ≤ 13846147449483^3383*80000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17536289 80000000 13846147449483 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (508114009/1000000000 : ℝ)^4407 ≤ (41396019083937/100000000000000 : ℝ)^3383 := by
    have hnat : (508114009 : ℕ)^4407*100000000000000^3383 ≤ 41396019083937^3383*1000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508114009 1000000000 41396019083937 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5395010431/10000000000 : ℝ), (-17536289/80000000 : ℝ), (508114009/1000000000 : ℝ)] ![(44757833458523/100000000000000 : ℝ), (13846147449483/100000000000000 : ℝ), (41396019083937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5395010431/10000000000 : ℝ)|^4407 ≤ (44757833458523/100000000000000 : ℝ)^3383
        have hw : |(5395010431/10000000000 : ℝ)|=(5395010431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-17536289/80000000 : ℝ)|^4407 ≤ (13846147449483/100000000000000 : ℝ)^3383
        have hw : |(-17536289/80000000 : ℝ)|=(17536289/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(508114009/1000000000 : ℝ)|^4407 ≤ (41396019083937/100000000000000 : ℝ)^3383
        have hw : |(508114009/1000000000 : ℝ)|=(508114009/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s1_2 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5395010449/10000000000 : ℝ)*x 0 + (2540569979/5000000000 : ℝ)*x 1 + (-2192036271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5395010449/10000000000 : ℝ)^4407 ≤ (8951566730611/20000000000000 : ℝ)^3383 := by
    have hnat : (5395010449 : ℕ)^4407*20000000000000^3383 ≤ 8951566730611^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395010449 10000000000 8951566730611 20000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2540569979/5000000000 : ℝ)^4407 ≤ (2069800884151/5000000000000 : ℝ)^3383 := by
    have hnat : (2540569979 : ℕ)^4407*5000000000000^3383 ≤ 2069800884151^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2540569979 5000000000 2069800884151 5000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2192036271/10000000000 : ℝ)^4407 ≤ (432692145339/3125000000000 : ℝ)^3383 := by
    have hnat : (2192036271 : ℕ)^4407*3125000000000^3383 ≤ 432692145339^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2192036271 10000000000 432692145339 3125000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5395010449/10000000000 : ℝ), (2540569979/5000000000 : ℝ), (-2192036271/10000000000 : ℝ)] ![(8951566730611/20000000000000 : ℝ), (2069800884151/5000000000000 : ℝ), (432692145339/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5395010449/10000000000 : ℝ)|^4407 ≤ (8951566730611/20000000000000 : ℝ)^3383
        have hw : |(5395010449/10000000000 : ℝ)|=(5395010449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2540569979/5000000000 : ℝ)|^4407 ≤ (2069800884151/5000000000000 : ℝ)^3383
        have hw : |(2540569979/5000000000 : ℝ)|=(2540569979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2192036271/10000000000 : ℝ)|^4407 ≤ (432692145339/3125000000000 : ℝ)^3383
        have hw : |(-2192036271/10000000000 : ℝ)|=(2192036271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s1_3 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (854672821/2000000000 : ℝ)*x 0 + (3743345361/10000000000 : ℝ)*x 1 + (243453003/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (854672821/2000000000 : ℝ)^4407 ≤ (16518768691651/50000000000000 : ℝ)^3383 := by
    have hnat : (854672821 : ℕ)^4407*50000000000000^3383 ≤ 16518768691651^3383*2000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854672821 2000000000 16518768691651 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3743345361/10000000000 : ℝ)^4407 ≤ (6950722944721/25000000000000 : ℝ)^3383 := by
    have hnat : (3743345361 : ℕ)^4407*25000000000000^3383 ≤ 6950722944721^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3743345361 10000000000 6950722944721 25000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (243453003/500000000 : ℝ)^4407 ≤ (39159570825363/100000000000000 : ℝ)^3383 := by
    have hnat : (243453003 : ℕ)^4407*100000000000000^3383 ≤ 39159570825363^3383*500000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243453003 500000000 39159570825363 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(854672821/2000000000 : ℝ), (3743345361/10000000000 : ℝ), (243453003/500000000 : ℝ)] ![(16518768691651/50000000000000 : ℝ), (6950722944721/25000000000000 : ℝ), (39159570825363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(854672821/2000000000 : ℝ)|^4407 ≤ (16518768691651/50000000000000 : ℝ)^3383
        have hw : |(854672821/2000000000 : ℝ)|=(854672821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3743345361/10000000000 : ℝ)|^4407 ≤ (6950722944721/25000000000000 : ℝ)^3383
        have hw : |(3743345361/10000000000 : ℝ)|=(3743345361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(243453003/500000000 : ℝ)|^4407 ≤ (39159570825363/100000000000000 : ℝ)^3383
        have hw : |(243453003/500000000 : ℝ)|=(243453003/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s1_4 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-9594277/50000000 : ℝ)*x 0 + (5087115903/10000000000 : ℝ)*x 1 + (1398003503/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9594277/50000000 : ℝ)^4407 ≤ (11641967005633/100000000000000 : ℝ)^3383 := by
    have hnat : (9594277 : ℕ)^4407*100000000000000^3383 ≤ 11641967005633^3383*50000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9594277 50000000 11641967005633 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5087115903/10000000000 : ℝ)^4407 ≤ (41459451716341/100000000000000 : ℝ)^3383 := by
    have hnat : (5087115903 : ℕ)^4407*100000000000000^3383 ≤ 41459451716341^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5087115903 10000000000 41459451716341 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1398003503/2500000000 : ℝ)^4407 ≤ (732790332217/1562500000000 : ℝ)^3383 := by
    have hnat : (1398003503 : ℕ)^4407*1562500000000^3383 ≤ 732790332217^3383*2500000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1398003503 2500000000 732790332217 1562500000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-9594277/50000000 : ℝ), (5087115903/10000000000 : ℝ), (1398003503/2500000000 : ℝ)] ![(11641967005633/100000000000000 : ℝ), (41459451716341/100000000000000 : ℝ), (732790332217/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-9594277/50000000 : ℝ)|^4407 ≤ (11641967005633/100000000000000 : ℝ)^3383
        have hw : |(-9594277/50000000 : ℝ)|=(9594277/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5087115903/10000000000 : ℝ)|^4407 ≤ (41459451716341/100000000000000 : ℝ)^3383
        have hw : |(5087115903/10000000000 : ℝ)|=(5087115903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1398003503/2500000000 : ℝ)|^4407 ≤ (732790332217/1562500000000 : ℝ)^3383
        have hw : |(1398003503/2500000000 : ℝ)|=(1398003503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s1_5 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5259767291/10000000000 : ℝ)*x 0 + (-1681161849/10000000000 : ℝ)*x 1 + (5592014041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5259767291/10000000000 : ℝ)^4407 ≤ (676590564927/1562500000000 : ℝ)^3383 := by
    have hnat : (5259767291 : ℕ)^4407*1562500000000^3383 ≤ 676590564927^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259767291 10000000000 676590564927 1562500000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1681161849/10000000000 : ℝ)^4407 ≤ (9799622250171/100000000000000 : ℝ)^3383 := by
    have hnat : (1681161849 : ℕ)^4407*100000000000000^3383 ≤ 9799622250171^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1681161849 10000000000 9799622250171 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5592014041/10000000000 : ℝ)^4407 ≤ (46898581578721/100000000000000 : ℝ)^3383 := by
    have hnat : (5592014041 : ℕ)^4407*100000000000000^3383 ≤ 46898581578721^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5592014041 10000000000 46898581578721 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5259767291/10000000000 : ℝ), (-1681161849/10000000000 : ℝ), (5592014041/10000000000 : ℝ)] ![(676590564927/1562500000000 : ℝ), (9799622250171/100000000000000 : ℝ), (46898581578721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5259767291/10000000000 : ℝ)|^4407 ≤ (676590564927/1562500000000 : ℝ)^3383
        have hw : |(5259767291/10000000000 : ℝ)|=(5259767291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1681161849/10000000000 : ℝ)|^4407 ≤ (9799622250171/100000000000000 : ℝ)^3383
        have hw : |(-1681161849/10000000000 : ℝ)|=(1681161849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5592014041/10000000000 : ℝ)|^4407 ≤ (46898581578721/100000000000000 : ℝ)^3383
        have hw : |(5592014041/10000000000 : ℝ)|=(5592014041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s1_6 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5259767201/10000000000 : ℝ)*x 0 + (5592014001/10000000000 : ℝ)*x 1 + (-1681162033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5259767201/10000000000 : ℝ)^4407 ≤ (10825448797529/25000000000000 : ℝ)^3383 := by
    have hnat : (5259767201 : ℕ)^4407*25000000000000^3383 ≤ 10825448797529^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259767201 10000000000 10825448797529 25000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5592014001/10000000000 : ℝ)^4407 ≤ (4689858114171/10000000000000 : ℝ)^3383 := by
    have hnat : (5592014001 : ℕ)^4407*10000000000000^3383 ≤ 4689858114171^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5592014001 10000000000 4689858114171 10000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1681162033/10000000000 : ℝ)^4407 ≤ (9799623647371/100000000000000 : ℝ)^3383 := by
    have hnat : (1681162033 : ℕ)^4407*100000000000000^3383 ≤ 9799623647371^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1681162033 10000000000 9799623647371 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5259767201/10000000000 : ℝ), (5592014001/10000000000 : ℝ), (-1681162033/10000000000 : ℝ)] ![(10825448797529/25000000000000 : ℝ), (4689858114171/10000000000000 : ℝ), (9799623647371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5259767201/10000000000 : ℝ)|^4407 ≤ (10825448797529/25000000000000 : ℝ)^3383
        have hw : |(5259767201/10000000000 : ℝ)|=(5259767201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5592014001/10000000000 : ℝ)|^4407 ≤ (4689858114171/10000000000000 : ℝ)^3383
        have hw : |(5592014001/10000000000 : ℝ)|=(5592014001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1681162033/10000000000 : ℝ)|^4407 ≤ (9799623647371/100000000000000 : ℝ)^3383
        have hw : |(-1681162033/10000000000 : ℝ)|=(1681162033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s1_7 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4274178737/10000000000 : ℝ)*x 0 + (4856047041/10000000000 : ℝ)*x 1 + (187828779/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4274178737/10000000000 : ℝ)^4407 ≤ (3304574189649/10000000000000 : ℝ)^3383 := by
    have hnat : (4274178737 : ℕ)^4407*10000000000000^3383 ≤ 3304574189649^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4274178737 10000000000 3304574189649 10000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4856047041/10000000000 : ℝ)^4407 ≤ (7804657915683/20000000000000 : ℝ)^3383 := by
    have hnat : (4856047041 : ℕ)^4407*20000000000000^3383 ≤ 7804657915683^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4856047041 10000000000 7804657915683 20000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (187828779/500000000 : ℝ)^4407 ≤ (27930968503041/100000000000000 : ℝ)^3383 := by
    have hnat : (187828779 : ℕ)^4407*100000000000000^3383 ≤ 27930968503041^3383*500000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187828779 500000000 27930968503041 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4274178737/10000000000 : ℝ), (4856047041/10000000000 : ℝ), (187828779/500000000 : ℝ)] ![(3304574189649/10000000000000 : ℝ), (7804657915683/20000000000000 : ℝ), (27930968503041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4274178737/10000000000 : ℝ)|^4407 ≤ (3304574189649/10000000000000 : ℝ)^3383
        have hw : |(4274178737/10000000000 : ℝ)|=(4274178737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4856047041/10000000000 : ℝ)|^4407 ≤ (7804657915683/20000000000000 : ℝ)^3383
        have hw : |(4856047041/10000000000 : ℝ)|=(4856047041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(187828779/500000000 : ℝ)|^4407 ≤ (27930968503041/100000000000000 : ℝ)^3383
        have hw : |(187828779/500000000 : ℝ)|=(187828779/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1447_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31776097/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13067/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1087/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (3899/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2341/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13067/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1087/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13067/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1087/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13067/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1087/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13067/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1087/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13067/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1087/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13067/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1087/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1087/50000 : ℝ) ^ (2203/512 : ℝ) ≤ (7009216344153/100000000000000000000 : ℝ) := by
    have hpowers : (1087/50000 : ℝ)^2203 ≤ (7009216344153/100000000000000000000 : ℝ)^512 := by
      have hnat : (1087 : ℕ)^2203*100000000000000000000^512 ≤ 7009216344153^512*50000^2203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1087 50000 7009216344153 100000000000000000000 2203 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1087/50000 : ℝ)) (X := (7009216344153/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have hpowhi : (13067/50000 : ℝ) ^ (2203/512 : ℝ) ≤ (77684029428805769/25000000000000000000 : ℝ) := by
    have hpowers : (13067/50000 : ℝ)^2203 ≤ (77684029428805769/25000000000000000000 : ℝ)^512 := by
      have hnat : (13067 : ℕ)^2203*25000000000000000000^512 ≤ 77684029428805769^512*50000^2203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13067 50000 77684029428805769 25000000000000000000 2203 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13067/50000 : ℝ)) (X := (77684029428805769/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000007009216344153/50000000000000000000 : ℝ) ≤ (10000000325802867/10000000000000000 : ℝ) ^ (2203/512 : ℝ) := by
    have hpowers : (50000007009216344153/50000000000000000000 : ℝ)^512 ≤ (10000000325802867/10000000000000000 : ℝ)^2203 := by
      have hnat : (50000007009216344153 : ℕ)^512*10000000000000000^2203 ≤ 10000000325802867^2203*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000007009216344153 50000000000000000000 10000000325802867 10000000000000000 512 2203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000325802867/10000000000000000 : ℝ)) (X := (50000007009216344153/50000000000000000000 : ℝ)) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100310743126931567229/100000000000000000000 : ℝ) ≤ (5003606697273293/5000000000000000 : ℝ) ^ (2203/512 : ℝ) := by
    have hpowers : (100310743126931567229/100000000000000000000 : ℝ)^512 ≤ (5003606697273293/5000000000000000 : ℝ)^2203 := by
      have hnat : (100310743126931567229 : ℕ)^512*5000000000000000^2203 ≤ 5003606697273293^2203*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100310743126931567229 100000000000000000000 5003606697273293 5000000000000000 512 2203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003606697273293/5000000000000000 : ℝ)) (X := (100310743126931567229/100000000000000000000 : ℝ)) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12577684029428805769/12500000000000000000 : ℝ) ≤ (2002885292658061/2000000000000000 : ℝ) ^ (2203/512 : ℝ) := by
    have hpowers : (12577684029428805769/12500000000000000000 : ℝ)^512 ≤ (2002885292658061/2000000000000000 : ℝ)^2203 := by
      have hnat : (12577684029428805769 : ℕ)^512*2000000000000000^2203 ≤ 2002885292658061^2203*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12577684029428805769 12500000000000000000 2002885292658061 2000000000000000 512 2203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002885292658061/2000000000000000 : ℝ)) (X := (12577684029428805769/12500000000000000000 : ℝ)) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7009216344153/100000000000000000000 : ℝ) ≤ ((59892161345834750777/59900000000000000000 : ℝ)+2*(7213068743719/2396000000000000 : ℝ)*(1087/50000 : ℝ))^(2203/512 : ℝ) := by
    rw [show (59892161345834750777/59900000000000000000 : ℝ)+2*(7213068743719/2396000000000000 : ℝ)*(1087/50000 : ℝ)=(10000000325802867/10000000000000000 : ℝ) by norm_num, show 1+2*(7009216344153/100000000000000000000 : ℝ)=(50000007009216344153/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(77684029428805769/25000000000000000000 : ℝ)+(7009216344153/100000000000000000000 : ℝ) ≤ ((59892161345834750777/59900000000000000000 : ℝ)+(7213068743719/2396000000000000 : ℝ)*((13067/50000 : ℝ)+(1087/50000 : ℝ)))^(2203/512 : ℝ) := by
    rw [show (59892161345834750777/59900000000000000000 : ℝ)+(7213068743719/2396000000000000 : ℝ)*((13067/50000 : ℝ)+(1087/50000 : ℝ))=(5003606697273293/5000000000000000 : ℝ) by norm_num, show 1+(77684029428805769/25000000000000000000 : ℝ)+(7009216344153/100000000000000000000 : ℝ)=(100310743126931567229/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(77684029428805769/25000000000000000000 : ℝ) ≤ ((59892161345834750777/59900000000000000000 : ℝ)+2*(7213068743719/2396000000000000 : ℝ)*(13067/50000 : ℝ))^(2203/512 : ℝ) := by
    rw [show (59892161345834750777/59900000000000000000 : ℝ)+2*(7213068743719/2396000000000000 : ℝ)*(13067/50000 : ℝ)=(2002885292658061/2000000000000000 : ℝ) by norm_num, show 1+2*(77684029428805769/25000000000000000000 : ℝ)=(12577684029428805769/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (59892161345834750777/59900000000000000000 : ℝ)*(X 1 0+X 2 0)+(7213068743719/2396000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2203/512 : ℝ)) (lo := (1087/50000 : ℝ)) (hi := (13067/50000 : ℝ)) (c := (59892161345834750777/59900000000000000000 : ℝ)) (alpha := (7213068743719/2396000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (59892161345834750777/59900000000000000000 : ℝ)*(X 0 1+X 2 1)+(7213068743719/2396000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2203/512 : ℝ)) (lo := (1087/50000 : ℝ)) (hi := (13067/50000 : ℝ)) (c := (59892161345834750777/59900000000000000000 : ℝ)) (alpha := (7213068743719/2396000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (59892161345834750777/59900000000000000000 : ℝ)*(X 0 2+X 1 2)+(7213068743719/2396000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2203/512 : ℝ)) (lo := (1087/50000 : ℝ)) (hi := (13067/50000 : ℝ)) (c := (59892161345834750777/59900000000000000000 : ℝ)) (alpha := (7213068743719/2396000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-383696269/2000000000 : ℝ)*X 0 0+(5598089883/10000000000 : ℝ)*X 0 1+(5081139849/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5395010431/10000000000 : ℝ)*X 1 0+(-17536289/80000000 : ℝ)*X 1 1+(508114009/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5395010449/10000000000 : ℝ)*X 2 0+(2540569979/5000000000 : ℝ)*X 2 1+(-2192036271/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((854672821/2000000000 : ℝ)*X 0 0+(3743345361/10000000000 : ℝ)*X 0 1+(243453003/500000000 : ℝ)*X 0 2+(854672821/2000000000 : ℝ)*X 1 0+(3743345361/10000000000 : ℝ)*X 1 1+(243453003/500000000 : ℝ)*X 1 2+(854672821/2000000000 : ℝ)*X 2 0+(3743345361/10000000000 : ℝ)*X 2 1+(243453003/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-9594277/50000000 : ℝ)*X 0 0+(5087115903/10000000000 : ℝ)*X 0 1+(1398003503/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5259767291/10000000000 : ℝ)*X 1 0+(-1681161849/10000000000 : ℝ)*X 1 1+(5592014041/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5259767201/10000000000 : ℝ)*X 2 0+(5592014001/10000000000 : ℝ)*X 2 1+(-1681162033/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4274178737/10000000000 : ℝ)*X 0 0+(4856047041/10000000000 : ℝ)*X 0 1+(187828779/500000000 : ℝ)*X 0 2+(4274178737/10000000000 : ℝ)*X 1 0+(4856047041/10000000000 : ℝ)*X 1 1+(187828779/500000000 : ℝ)*X 1 2+(4274178737/10000000000 : ℝ)*X 2 0+(4856047041/10000000000 : ℝ)*X 2 1+(187828779/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4033523356015517794384120941/599000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4437317/12500000000000 : ℝ)*(base1) + (3831867/312500000000 : ℝ)*(base19) + (77040721/6250000000000 : ℝ)*(base23) + (17783277/10000000000000 : ℝ)*(upper3) + (55620963/50000000000000 : ℝ)*(upper5) + (282277406983689/20000000000000 : ℝ)*(major0) + (282277406983689/20000000000000 : ℝ)*(major1) + (282277406983689/20000000000000 : ℝ)*(major2) + (967216232165309/50000000000000 : ℝ)*(sp0) + (386888017478431/20000000000000 : ℝ)*(sp1) + (96722004046903/5000000000000 : ℝ)*(sp2) + (888328296056797/100000000000000 : ℝ)*(sp3) + (4442378757/50000000000000 : ℝ)*(sp4) + (1050058307/25000000000000 : ℝ)*(sp7) + (888332531788561/100000000000000 : ℝ)*(f.failure) + (386888262717919/20000000000000 : ℝ)*(f.sum) + (27535394251831/23960000000000000000000000000 : ℝ)*base65 + (696126481794148647/1198000000000000000000000000000000 : ℝ)*base68 + (404532413423851353/1198000000000000000000000000000000 : ℝ)*base69 + (7585307735455851353/1198000000000000000000000000000000 : ℝ)*base71 + (26503984453009/23960000000000000000000000000 : ℝ)*base74 + (4500361315623851353/1198000000000000000000000000000000 : ℝ)*base75 + (6322537986274148647/1198000000000000000000000000000000 : ℝ)*base78 + (4062426982693851353/1198000000000000000000000000000000 : ℝ)*base79 + (117996904031391/23960000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (2173583/2000000000000000000000 : ℝ)*base90 + (2173583/2000000000000000000000 : ℝ)*base92 + (2173583/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (379900484235854673859059/59900000000000000000000000000 : ℝ) := by norm_num
    linear_combination (43293353/100000000000000 : ℝ)*(base1) + (700764663/50000000000000 : ℝ)*(base19) + (54238251/4000000000000 : ℝ)*(base23) + (161101889/100000000000000 : ℝ)*(upper3) + (126322763/100000000000000 : ℝ)*(upper5) + (722531326472787/50000000000000 : ℝ)*(major0) + (722531326472787/50000000000000 : ℝ)*(major1) + (722531326472787/50000000000000 : ℝ)*(major2) + (4288966933/50000000000000 : ℝ)*(sp1) + (8123560291/100000000000000 : ℝ)*(sp2) + (1980597040008009/100000000000000 : ℝ)*(sp4) + (247573377156433/12500000000000 : ℝ)*(sp5) + (198058751719809/10000000000000 : ℝ)*(sp6) + (454764027237481/50000000000000 : ℝ)*(sp7) + (227382024442079/25000000000000 : ℝ)*(f.failure) + (61893656147333/3125000000000 : ℝ)*(f.sum) + (33992894525747/59900000000000000000000000000 : ℝ)*base66 + (2644990152666069501/2995000000000000000000000000000000 : ℝ)*base68 + (12571719827828930499/2995000000000000000000000000000000 : ℝ)*base69 + (4246059505808930499/2995000000000000000000000000000000 : ℝ)*base71 + (130623386559547/59900000000000000000000000000 : ℝ)*base74 + (20064411380891069501/2995000000000000000000000000000000 : ℝ)*base76 + (6718954398796069501/2995000000000000000000000000000000 : ℝ)*base78 + (16638620618038930499/2995000000000000000000000000000000 : ℝ)*base79 + (275761282547753/59900000000000000000000000000 : ℝ)*base81 + (3185663/500000000000000000000 : ℝ)*base89 + (3185663/500000000000000000000 : ℝ)*base91 + (3185663/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1447_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31776097/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13067/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1087/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3899/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2341/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1447_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1447_s2_0 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1950290911/10000000000 : ℝ)*x 0 + (1363555633/2500000000 : ℝ)*x 1 + (5082531/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1950290911/10000000000 : ℝ)^4407 ≤ (371594828753/3125000000000 : ℝ)^3383 := by
    have hnat : (1950290911 : ℕ)^4407*3125000000000^3383 ≤ 371594828753^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1950290911 10000000000 371594828753 3125000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1363555633/2500000000 : ℝ)^4407 ≤ (22699408777673/50000000000000 : ℝ)^3383 := by
    have hnat : (1363555633 : ℕ)^4407*50000000000000^3383 ≤ 22699408777673^3383*2500000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363555633 2500000000 22699408777673 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5082531/9765625 : ℝ)^4407 ≤ (42710147919413/100000000000000 : ℝ)^3383 := by
    have hnat : (5082531 : ℕ)^4407*100000000000000^3383 ≤ 42710147919413^3383*9765625^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5082531 9765625 42710147919413 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1950290911/10000000000 : ℝ), (1363555633/2500000000 : ℝ), (5082531/9765625 : ℝ)] ![(371594828753/3125000000000 : ℝ), (22699408777673/50000000000000 : ℝ), (42710147919413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1950290911/10000000000 : ℝ)|^4407 ≤ (371594828753/3125000000000 : ℝ)^3383
        have hw : |(-1950290911/10000000000 : ℝ)|=(1950290911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1363555633/2500000000 : ℝ)|^4407 ≤ (22699408777673/50000000000000 : ℝ)^3383
        have hw : |(1363555633/2500000000 : ℝ)|=(1363555633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5082531/9765625 : ℝ)|^4407 ≤ (42710147919413/100000000000000 : ℝ)^3383
        have hw : |(5082531/9765625 : ℝ)|=(5082531/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s2_1 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2679506041/5000000000 : ℝ)*x 0 + (-2078666573/10000000000 : ℝ)*x 1 + (1301127851/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2679506041/5000000000 : ℝ)^4407 ≤ (44369181442383/100000000000000 : ℝ)^3383 := by
    have hnat : (2679506041 : ℕ)^4407*100000000000000^3383 ≤ 44369181442383^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2679506041 5000000000 44369181442383 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2078666573/10000000000 : ℝ)^4407 ≤ (6460337127257/50000000000000 : ℝ)^3383 := by
    have hnat : (2078666573 : ℕ)^4407*50000000000000^3383 ≤ 6460337127257^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078666573 10000000000 6460337127257 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1301127851/2500000000 : ℝ)^4407 ≤ (42710144284693/100000000000000 : ℝ)^3383 := by
    have hnat : (1301127851 : ℕ)^4407*100000000000000^3383 ≤ 42710144284693^3383*2500000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301127851 2500000000 42710144284693 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2679506041/5000000000 : ℝ), (-2078666573/10000000000 : ℝ), (1301127851/2500000000 : ℝ)] ![(44369181442383/100000000000000 : ℝ), (6460337127257/50000000000000 : ℝ), (42710144284693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2679506041/5000000000 : ℝ)|^4407 ≤ (44369181442383/100000000000000 : ℝ)^3383
        have hw : |(2679506041/5000000000 : ℝ)|=(2679506041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2078666573/10000000000 : ℝ)|^4407 ≤ (6460337127257/50000000000000 : ℝ)^3383
        have hw : |(-2078666573/10000000000 : ℝ)|=(2078666573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1301127851/2500000000 : ℝ)|^4407 ≤ (42710144284693/100000000000000 : ℝ)^3383
        have hw : |(1301127851/2500000000 : ℝ)|=(1301127851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s2_2 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071802291/2000000000 : ℝ)*x 0 + (1040902399/2000000000 : ℝ)*x 1 + (-2078666629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071802291/2000000000 : ℝ)^4407 ≤ (22184587339957/50000000000000 : ℝ)^3383 := by
    have hnat : (1071802291 : ℕ)^4407*50000000000000^3383 ≤ 22184587339957^3383*2000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071802291 2000000000 22184587339957 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1040902399/2000000000 : ℝ)^4407 ≤ (42710150602693/100000000000000 : ℝ)^3383 := by
    have hnat : (1040902399 : ℕ)^4407*100000000000000^3383 ≤ 42710150602693^3383*2000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040902399 2000000000 42710150602693 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2078666629/10000000000 : ℝ)^4407 ≤ (3230168676991/25000000000000 : ℝ)^3383 := by
    have hnat : (2078666629 : ℕ)^4407*25000000000000^3383 ≤ 3230168676991^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078666629 10000000000 3230168676991 25000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071802291/2000000000 : ℝ), (1040902399/2000000000 : ℝ), (-2078666629/10000000000 : ℝ)] ![(22184587339957/50000000000000 : ℝ), (42710150602693/100000000000000 : ℝ), (3230168676991/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071802291/2000000000 : ℝ)|^4407 ≤ (22184587339957/50000000000000 : ℝ)^3383
        have hw : |(1071802291/2000000000 : ℝ)|=(1071802291/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1040902399/2000000000 : ℝ)|^4407 ≤ (42710150602693/100000000000000 : ℝ)^3383
        have hw : |(1040902399/2000000000 : ℝ)|=(1040902399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2078666629/10000000000 : ℝ)|^4407 ≤ (3230168676991/25000000000000 : ℝ)^3383
        have hw : |(-2078666629/10000000000 : ℝ)|=(2078666629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s2_3 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2147930133/5000000000 : ℝ)*x 0 + (2015818787/5000000000 : ℝ)*x 1 + (4575411659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2147930133/5000000000 : ℝ)^4407 ≤ (1663213987773/5000000000000 : ℝ)^3383 := by
    have hnat : (2147930133 : ℕ)^4407*5000000000000^3383 ≤ 1663213987773^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147930133 5000000000 1663213987773 5000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2015818787/5000000000 : ℝ)^4407 ≤ (30624196727759/100000000000000 : ℝ)^3383 := by
    have hnat : (2015818787 : ℕ)^4407*100000000000000^3383 ≤ 30624196727759^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015818787 5000000000 30624196727759 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4575411659/10000000000 : ℝ)^4407 ≤ (36111523498237/100000000000000 : ℝ)^3383 := by
    have hnat : (4575411659 : ℕ)^4407*100000000000000^3383 ≤ 36111523498237^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4575411659 10000000000 36111523498237 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2147930133/5000000000 : ℝ), (2015818787/5000000000 : ℝ), (4575411659/10000000000 : ℝ)] ![(1663213987773/5000000000000 : ℝ), (30624196727759/100000000000000 : ℝ), (36111523498237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2147930133/5000000000 : ℝ)|^4407 ≤ (1663213987773/5000000000000 : ℝ)^3383
        have hw : |(2147930133/5000000000 : ℝ)|=(2147930133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2015818787/5000000000 : ℝ)|^4407 ≤ (30624196727759/100000000000000 : ℝ)^3383
        have hw : |(2015818787/5000000000 : ℝ)|=(2015818787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4575411659/10000000000 : ℝ)|^4407 ≤ (36111523498237/100000000000000 : ℝ)^3383
        have hw : |(4575411659/10000000000 : ℝ)|=(4575411659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s2_4 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-975166407/5000000000 : ℝ)*x 0 + (5205915673/10000000000 : ℝ)*x 1 + (5452807571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (975166407/5000000000 : ℝ)^4407 ≤ (11891367338877/100000000000000 : ℝ)^3383 := by
    have hnat : (975166407 : ℕ)^4407*100000000000000^3383 ≤ 11891367338877^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      975166407 5000000000 11891367338877 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5205915673/10000000000 : ℝ)^4407 ≤ (2670322314487/6250000000000 : ℝ)^3383 := by
    have hnat : (5205915673 : ℕ)^4407*6250000000000^3383 ≤ 2670322314487^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5205915673 10000000000 2670322314487 6250000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5452807571/10000000000 : ℝ)^4407 ≤ (22691737809829/50000000000000 : ℝ)^3383 := by
    have hnat : (5452807571 : ℕ)^4407*50000000000000^3383 ≤ 22691737809829^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452807571 10000000000 22691737809829 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-975166407/5000000000 : ℝ), (5205915673/10000000000 : ℝ), (5452807571/10000000000 : ℝ)] ![(11891367338877/100000000000000 : ℝ), (2670322314487/6250000000000 : ℝ), (22691737809829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-975166407/5000000000 : ℝ)|^4407 ≤ (11891367338877/100000000000000 : ℝ)^3383
        have hw : |(-975166407/5000000000 : ℝ)|=(975166407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5205915673/10000000000 : ℝ)|^4407 ≤ (2670322314487/6250000000000 : ℝ)^3383
        have hw : |(5205915673/10000000000 : ℝ)|=(5205915673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5452807571/10000000000 : ℝ)|^4407 ≤ (22691737809829/50000000000000 : ℝ)^3383
        have hw : |(5452807571/10000000000 : ℝ)|=(5452807571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s2_5 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058794081/2000000000 : ℝ)*x 0 + (-1830368991/10000000000 : ℝ)*x 1 + (1090561769/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058794081/2000000000 : ℝ)^4407 ≤ (5458621345921/12500000000000 : ℝ)^3383 := by
    have hnat : (1058794081 : ℕ)^4407*12500000000000^3383 ≤ 5458621345921^3383*2000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058794081 2000000000 5458621345921 12500000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1830368991/10000000000 : ℝ)^4407 ≤ (10947539789413/100000000000000 : ℝ)^3383 := by
    have hnat : (1830368991 : ℕ)^4407*100000000000000^3383 ≤ 10947539789413^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1830368991 10000000000 10947539789413 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1090561769/2000000000 : ℝ)^4407 ≤ (2269174471633/5000000000000 : ℝ)^3383 := by
    have hnat : (1090561769 : ℕ)^4407*5000000000000^3383 ≤ 2269174471633^3383*2000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090561769 2000000000 2269174471633 5000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058794081/2000000000 : ℝ), (-1830368991/10000000000 : ℝ), (1090561769/2000000000 : ℝ)] ![(5458621345921/12500000000000 : ℝ), (10947539789413/100000000000000 : ℝ), (2269174471633/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058794081/2000000000 : ℝ)|^4407 ≤ (5458621345921/12500000000000 : ℝ)^3383
        have hw : |(1058794081/2000000000 : ℝ)|=(1058794081/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1830368991/10000000000 : ℝ)|^4407 ≤ (10947539789413/100000000000000 : ℝ)^3383
        have hw : |(-1830368991/10000000000 : ℝ)|=(1830368991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1090561769/2000000000 : ℝ)|^4407 ≤ (2269174471633/5000000000000 : ℝ)^3383
        have hw : |(1090561769/2000000000 : ℝ)|=(1090561769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s2_6 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293969513/10000000000 : ℝ)*x 0 + (2726404261/5000000000 : ℝ)*x 1 + (-183037067/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293969513/10000000000 : ℝ)^4407 ≤ (43668961182253/100000000000000 : ℝ)^3383 := by
    have hnat : (5293969513 : ℕ)^4407*100000000000000^3383 ≤ 43668961182253^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293969513 10000000000 43668961182253 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2726404261/5000000000 : ℝ)^4407 ≤ (2269174296531/5000000000000 : ℝ)^3383 := by
    have hnat : (2726404261 : ℕ)^4407*5000000000000^3383 ≤ 2269174296531^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2726404261 5000000000 2269174296531 5000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (183037067/1000000000 : ℝ)^4407 ≤ (10947552871279/100000000000000 : ℝ)^3383 := by
    have hnat : (183037067 : ℕ)^4407*100000000000000^3383 ≤ 10947552871279^3383*1000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183037067 1000000000 10947552871279 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293969513/10000000000 : ℝ), (2726404261/5000000000 : ℝ), (-183037067/1000000000 : ℝ)] ![(43668961182253/100000000000000 : ℝ), (2269174296531/5000000000000 : ℝ), (10947552871279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293969513/10000000000 : ℝ)|^4407 ≤ (43668961182253/100000000000000 : ℝ)^3383
        have hw : |(5293969513/10000000000 : ℝ)|=(5293969513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2726404261/5000000000 : ℝ)|^4407 ≤ (2269174296531/5000000000000 : ℝ)^3383
        have hw : |(2726404261/5000000000 : ℝ)|=(2726404261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-183037067/1000000000 : ℝ)|^4407 ≤ (10947552871279/100000000000000 : ℝ)^3383
        have hw : |(-183037067/1000000000 : ℝ)|=(183037067/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s2_7 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1073988069/2500000000 : ℝ)*x 0 + (1143089089/2500000000 : ℝ)*x 1 + (806943537/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073988069/2500000000 : ℝ)^4407 ≤ (33265207878319/100000000000000 : ℝ)^3383 := by
    have hnat : (1073988069 : ℕ)^4407*100000000000000^3383 ≤ 33265207878319^3383*2500000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073988069 2500000000 33265207878319 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1143089089/2500000000 : ℝ)^4407 ≤ (7216022712097/20000000000000 : ℝ)^3383 := by
    have hnat : (1143089089 : ℕ)^4407*20000000000000^3383 ≤ 7216022712097^3383*2500000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1143089089 2500000000 7216022712097 20000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (806943537/2000000000 : ℝ)^4407 ≤ (3831834818047/12500000000000 : ℝ)^3383 := by
    have hnat : (806943537 : ℕ)^4407*12500000000000^3383 ≤ 3831834818047^3383*2000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806943537 2000000000 3831834818047 12500000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073988069/2500000000 : ℝ), (1143089089/2500000000 : ℝ), (806943537/2000000000 : ℝ)] ![(33265207878319/100000000000000 : ℝ), (7216022712097/20000000000000 : ℝ), (3831834818047/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073988069/2500000000 : ℝ)|^4407 ≤ (33265207878319/100000000000000 : ℝ)^3383
        have hw : |(1073988069/2500000000 : ℝ)|=(1073988069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1143089089/2500000000 : ℝ)|^4407 ≤ (7216022712097/20000000000000 : ℝ)^3383
        have hw : |(1143089089/2500000000 : ℝ)|=(1143089089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(806943537/2000000000 : ℝ)|^4407 ≤ (3831834818047/12500000000000 : ℝ)^3383
        have hw : |(806943537/2000000000 : ℝ)|=(806943537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1447_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31776097/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2341/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3899/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5231/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7873/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2341/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3899/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2341/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3899/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2341/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3899/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2341/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3899/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2341/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3899/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2341/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3899/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have hpowlo : (3899/50000 : ℝ) ^ (2203/512 : ℝ) ≤ (1708040480780183/100000000000000000000 : ℝ) := by
    have hpowers : (3899/50000 : ℝ)^2203 ≤ (1708040480780183/100000000000000000000 : ℝ)^512 := by
      have hnat : (3899 : ℕ)^2203*100000000000000000000^512 ≤ 1708040480780183^512*50000^2203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3899 50000 1708040480780183 100000000000000000000 2203 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3899/50000 : ℝ)) (X := (1708040480780183/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2341/12500 : ℝ) ^ (2203/512 : ℝ) ≤ (18520970939542643/25000000000000000000 : ℝ) := by
    have hpowers : (2341/12500 : ℝ)^2203 ≤ (18520970939542643/25000000000000000000 : ℝ)^512 := by
      have hnat : (2341 : ℕ)^2203*25000000000000000000^512 ≤ 18520970939542643^512*12500^2203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2341 12500 18520970939542643 25000000000000000000 2203 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2341/12500 : ℝ)) (X := (18520970939542643/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001708040480780183/50000000000000000000 : ℝ) ≤ (2000015878443229/2000000000000000 : ℝ) ^ (2203/512 : ℝ) := by
    have hpowers : (50001708040480780183/50000000000000000000 : ℝ)^512 ≤ (2000015878443229/2000000000000000 : ℝ)^2203 := by
      have hnat : (50001708040480780183 : ℕ)^512*2000000000000000^2203 ≤ 2000015878443229^2203*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001708040480780183 50000000000000000000 2000015878443229 2000000000000000 512 2203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000015878443229/2000000000000000 : ℝ)) (X := (50001708040480780183/50000000000000000000 : ℝ)) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20015158384847790151/20000000000000000000 : ℝ) ≤ (5000880485299637/5000000000000000 : ℝ) ^ (2203/512 : ℝ) := by
    have hpowers : (20015158384847790151/20000000000000000000 : ℝ)^512 ≤ (5000880485299637/5000000000000000 : ℝ)^2203 := by
      have hnat : (20015158384847790151 : ℕ)^512*5000000000000000^2203 ≤ 5000880485299637^2203*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20015158384847790151 20000000000000000000 5000880485299637 5000000000000000 512 2203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000880485299637/5000000000000000 : ℝ)) (X := (20015158384847790151/20000000000000000000 : ℝ)) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12518520970939542643/12500000000000000000 : ℝ) ≤ (10003442548982403/10000000000000000 : ℝ) ^ (2203/512 : ℝ) := by
    have hpowers : (12518520970939542643/12500000000000000000 : ℝ)^512 ≤ (10003442548982403/10000000000000000 : ℝ)^2203 := by
      have hnat : (12518520970939542643 : ℕ)^512*10000000000000000^2203 ≤ 10003442548982403^2203*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12518520970939542643 12500000000000000000 10003442548982403 10000000000000000 512 2203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003442548982403/10000000000000000 : ℝ)) (X := (12518520970939542643/12500000000000000000 : ℝ)) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1708040480780183/100000000000000000000 : ℝ) ≤ ((54637320930229592483/54650000000000000000 : ℝ)+2*(1681578383129/1093000000000000 : ℝ)*(3899/50000 : ℝ))^(2203/512 : ℝ) := by
    rw [show (54637320930229592483/54650000000000000000 : ℝ)+2*(1681578383129/1093000000000000 : ℝ)*(3899/50000 : ℝ)=(2000015878443229/2000000000000000 : ℝ) by norm_num, show 1+2*(1708040480780183/100000000000000000000 : ℝ)=(50001708040480780183/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18520970939542643/25000000000000000000 : ℝ)+(1708040480780183/100000000000000000000 : ℝ) ≤ ((54637320930229592483/54650000000000000000 : ℝ)+(1681578383129/1093000000000000 : ℝ)*((2341/12500 : ℝ)+(3899/50000 : ℝ)))^(2203/512 : ℝ) := by
    rw [show (54637320930229592483/54650000000000000000 : ℝ)+(1681578383129/1093000000000000 : ℝ)*((2341/12500 : ℝ)+(3899/50000 : ℝ))=(5000880485299637/5000000000000000 : ℝ) by norm_num, show 1+(18520970939542643/25000000000000000000 : ℝ)+(1708040480780183/100000000000000000000 : ℝ)=(20015158384847790151/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18520970939542643/25000000000000000000 : ℝ) ≤ ((54637320930229592483/54650000000000000000 : ℝ)+2*(1681578383129/1093000000000000 : ℝ)*(2341/12500 : ℝ))^(2203/512 : ℝ) := by
    rw [show (54637320930229592483/54650000000000000000 : ℝ)+2*(1681578383129/1093000000000000 : ℝ)*(2341/12500 : ℝ)=(10003442548982403/10000000000000000 : ℝ) by norm_num, show 1+2*(18520970939542643/25000000000000000000 : ℝ)=(12518520970939542643/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (54637320930229592483/54650000000000000000 : ℝ)*(X 1 0+X 2 0)+(1681578383129/1093000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2203/512 : ℝ)) (lo := (3899/50000 : ℝ)) (hi := (2341/12500 : ℝ)) (c := (54637320930229592483/54650000000000000000 : ℝ)) (alpha := (1681578383129/1093000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (54637320930229592483/54650000000000000000 : ℝ)*(X 0 1+X 2 1)+(1681578383129/1093000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2203/512 : ℝ)) (lo := (3899/50000 : ℝ)) (hi := (2341/12500 : ℝ)) (c := (54637320930229592483/54650000000000000000 : ℝ)) (alpha := (1681578383129/1093000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (54637320930229592483/54650000000000000000 : ℝ)*(X 0 2+X 1 2)+(1681578383129/1093000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2203/512 : ℝ)) (lo := (3899/50000 : ℝ)) (hi := (2341/12500 : ℝ)) (c := (54637320930229592483/54650000000000000000 : ℝ)) (alpha := (1681578383129/1093000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1950290911/10000000000 : ℝ)*X 0 0+(1363555633/2500000000 : ℝ)*X 0 1+(5082531/9765625 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2679506041/5000000000 : ℝ)*X 1 0+(-2078666573/10000000000 : ℝ)*X 1 1+(1301127851/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1071802291/2000000000 : ℝ)*X 2 0+(1040902399/2000000000 : ℝ)*X 2 1+(-2078666629/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2147930133/5000000000 : ℝ)*X 0 0+(2015818787/5000000000 : ℝ)*X 0 1+(4575411659/10000000000 : ℝ)*X 0 2+(2147930133/5000000000 : ℝ)*X 1 0+(2015818787/5000000000 : ℝ)*X 1 1+(4575411659/10000000000 : ℝ)*X 1 2+(2147930133/5000000000 : ℝ)*X 2 0+(2015818787/5000000000 : ℝ)*X 2 1+(4575411659/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-975166407/5000000000 : ℝ)*X 0 0+(5205915673/10000000000 : ℝ)*X 0 1+(5452807571/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1058794081/2000000000 : ℝ)*X 1 0+(-1830368991/10000000000 : ℝ)*X 1 1+(1090561769/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293969513/10000000000 : ℝ)*X 2 0+(2726404261/5000000000 : ℝ)*X 2 1+(-183037067/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1073988069/2500000000 : ℝ)*X 0 0+(1143089089/2500000000 : ℝ)*X 0 1+(806943537/2000000000 : ℝ)*X 0 2+(1073988069/2500000000 : ℝ)*X 1 0+(1143089089/2500000000 : ℝ)*X 1 1+(806943537/2000000000 : ℝ)*X 1 2+(1073988069/2500000000 : ℝ)*X 2 0+(1143089089/2500000000 : ℝ)*X 2 1+(806943537/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (98876561504487416685363/27325000000000000000000000000 : ℝ) := by norm_num
    linear_combination (85523581/100000000000000 : ℝ)*(base21) + (53340013/100000000000000 : ℝ)*(upper2) + (74913979/50000000000000 : ℝ)*(lower4) + (31681937/25000000000000 : ℝ)*(upper5) + (730454853036963/25000000000000 : ℝ)*(major0) + (730454853036963/25000000000000 : ℝ)*(major1) + (730454853036963/25000000000000 : ℝ)*(major2) + (4004634113436319/100000000000000 : ℝ)*(sp0) + (2002314314894493/50000000000000 : ℝ)*(sp1) + (500578726226033/12500000000000 : ℝ)*(sp2) + (1839003286049969/100000000000000 : ℝ)*(sp3) + (5483647333/100000000000000 : ℝ)*(sp5) + (2109052237/50000000000000 : ℝ)*(sp6) + (163023933/12500000000000 : ℝ)*(sp7) + (1839004590241433/100000000000000 : ℝ)*(f.failure) + (4004634113436319/100000000000000 : ℝ)*(f.sum) + (126038838208529/27325000000000000000000000000 : ℝ)*base65 + (45077332605200871/1366250000000000000000000000000000 : ℝ)*base68 + (4521149246948549129/1366250000000000000000000000000000 : ℝ)*base69 + (2583696124656450871/1366250000000000000000000000000000 : ℝ)*base72 + (28982914781471/27325000000000000000000000000 : ℝ)*base74 + (2387030687512299129/1366250000000000000000000000000000 : ℝ)*base75 + (7402421093412299129/1366250000000000000000000000000000 : ℝ)*base77 + (8399305881605200871/1366250000000000000000000000000000 : ℝ)*base80 + (96795006592579/27325000000000000000000000000 : ℝ)*base81 + (11572999/2000000000000000000000 : ℝ)*base90 + (11572999/2000000000000000000000 : ℝ)*base92 + (11572999/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (954191856196533594856360089/85390625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (128656363/20000000000000 : ℝ)*(base19) + (294283159/100000000000000 : ℝ)*(base23) + (251606901/100000000000000 : ℝ)*(upper3) + (57609483/20000000000000 : ℝ)*(lower4) + (46174484742809/1562500000000 : ℝ)*(major0) + (46174484742809/1562500000000 : ℝ)*(major1) + (46174484742809/1562500000000 : ℝ)*(major2) + (11214754087/50000000000000 : ℝ)*(sp1) + (5284176643/100000000000000 : ℝ)*(sp2) + (4818784707/100000000000000 : ℝ)*(sp3) + (101258499175977/2500000000000 : ℝ)*(sp4) + (4050316894249091/100000000000000 : ℝ)*(sp5) + (2025167194289639/50000000000000 : ℝ)*(sp6) + (929994444387321/50000000000000 : ℝ)*(sp7) + (37199874151187/2000000000000 : ℝ)*(f.failure) + (101258499175977/2500000000000 : ℝ)*(f.sum) + (99633472404001/13662500000000000000000000000 : ℝ)*base65 + (231315079673026503/85390625000000000000000000000000 : ℝ)*base68 + (69781389746520891/10673828125000000000000000000000 : ℝ)*base70 + (112512991588057061/42695312500000000000000000000000 : ℝ)*base71 + (105778983612277/27325000000000000000000000000 : ℝ)*base73 + (972852618091151503/85390625000000000000000000000000 : ℝ)*base76 + (13868850295067939/42695312500000000000000000000000 : ℝ)*base78 + (245001584247807407/21347656250000000000000000000000 : ℝ)*base80 + (16393372634419/3415625000000000000000000000 : ℝ)*base81 + (377139/40000000000000000000 : ℝ)*base89 + (377139/40000000000000000000 : ℝ)*base91 + (377139/40000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1447_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31776097/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2341/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3899/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5231/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7873/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1447_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1447_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31776097/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5231/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7873/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1447_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1447_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1447_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31776097/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5231/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7873/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1447_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

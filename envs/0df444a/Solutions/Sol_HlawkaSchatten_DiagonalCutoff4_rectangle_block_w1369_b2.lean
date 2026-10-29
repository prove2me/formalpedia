-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1369_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:20:32.673102+00:00
-- url     : https://prove2.me/submissions/771a71b1-3967-44b4-8ae0-67704602c751

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
theorem support_rectangle_w1369_s6_0 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-404174249/2000000000 : ℝ)*x 0 + (541132261/1000000000 : ℝ)*x 1 + (1311348237/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (404174249/2000000000 : ℝ)^4329 ≤ (6156603670287/50000000000000 : ℝ)^3305 := by
    have hnat : (404174249 : ℕ)^4329*50000000000000^3305 ≤ 6156603670287^3305*2000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404174249 2000000000 6156603670287 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541132261/1000000000 : ℝ)^4329 ≤ (8947503280517/20000000000000 : ℝ)^3305 := by
    have hnat : (541132261 : ℕ)^4329*20000000000000^3305 ≤ 8947503280517^3305*1000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541132261 1000000000 8947503280517 20000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311348237/2500000000 : ℝ)^4329 ≤ (21474638121311/50000000000000 : ℝ)^3305 := by
    have hnat : (1311348237 : ℕ)^4329*50000000000000^3305 ≤ 21474638121311^3305*2500000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311348237 2500000000 21474638121311 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-404174249/2000000000 : ℝ), (541132261/1000000000 : ℝ), (1311348237/2500000000 : ℝ)] ![(6156603670287/50000000000000 : ℝ), (8947503280517/20000000000000 : ℝ), (21474638121311/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-404174249/2000000000 : ℝ)|^4329 ≤ (6156603670287/50000000000000 : ℝ)^3305
        have hw : |(-404174249/2000000000 : ℝ)|=(404174249/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541132261/1000000000 : ℝ)|^4329 ≤ (8947503280517/20000000000000 : ℝ)^3305
        have hw : |(541132261/1000000000 : ℝ)|=(541132261/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311348237/2500000000 : ℝ)|^4329 ≤ (21474638121311/50000000000000 : ℝ)^3305
        have hw : |(1311348237/2500000000 : ℝ)|=(1311348237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s6_1 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674258989/5000000000 : ℝ)*x 0 + (-2105391641/10000000000 : ℝ)*x 1 + (1049078707/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674258989/5000000000 : ℝ)^4329 ≤ (11014659269033/25000000000000 : ℝ)^3305 := by
    have hnat : (2674258989 : ℕ)^4329*25000000000000^3305 ≤ 11014659269033^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674258989 5000000000 11014659269033 25000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2105391641/10000000000 : ℝ)^4329 ≤ (6496040189829/50000000000000 : ℝ)^3305 := by
    have hnat : (2105391641 : ℕ)^4329*50000000000000^3305 ≤ 6496040189829^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105391641 10000000000 6496040189829 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049078707/2000000000 : ℝ)^4329 ≤ (10737320634537/25000000000000 : ℝ)^3305 := by
    have hnat : (1049078707 : ℕ)^4329*25000000000000^3305 ≤ 10737320634537^3305*2000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049078707 2000000000 10737320634537 25000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674258989/5000000000 : ℝ), (-2105391641/10000000000 : ℝ), (1049078707/2000000000 : ℝ)] ![(11014659269033/25000000000000 : ℝ), (6496040189829/50000000000000 : ℝ), (10737320634537/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674258989/5000000000 : ℝ)|^4329 ≤ (11014659269033/25000000000000 : ℝ)^3305
        have hw : |(2674258989/5000000000 : ℝ)|=(2674258989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2105391641/10000000000 : ℝ)|^4329 ≤ (6496040189829/50000000000000 : ℝ)^3305
        have hw : |(-2105391641/10000000000 : ℝ)|=(2105391641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049078707/2000000000 : ℝ)|^4329 ≤ (10737320634537/25000000000000 : ℝ)^3305
        have hw : |(1049078707/2000000000 : ℝ)|=(1049078707/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s6_2 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42788143/80000000 : ℝ)*x 0 + (1311348399/2500000000 : ℝ)*x 1 + (-131586981/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42788143/80000000 : ℝ)^4329 ≤ (44058635964781/100000000000000 : ℝ)^3305 := by
    have hnat : (42788143 : ℕ)^4329*100000000000000^3305 ≤ 44058635964781^3305*80000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42788143 80000000 44058635964781 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311348399/2500000000 : ℝ)^4329 ≤ (2684330199523/6250000000000 : ℝ)^3305 := by
    have hnat : (1311348399 : ℕ)^4329*6250000000000^3305 ≤ 2684330199523^3305*2500000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311348399 2500000000 2684330199523 6250000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131586981/625000000 : ℝ)^4329 ≤ (3248020206053/25000000000000 : ℝ)^3305 := by
    have hnat : (131586981 : ℕ)^4329*25000000000000^3305 ≤ 3248020206053^3305*625000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131586981 625000000 3248020206053 25000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42788143/80000000 : ℝ), (1311348399/2500000000 : ℝ), (-131586981/625000000 : ℝ)] ![(44058635964781/100000000000000 : ℝ), (2684330199523/6250000000000 : ℝ), (3248020206053/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42788143/80000000 : ℝ)|^4329 ≤ (44058635964781/100000000000000 : ℝ)^3305
        have hw : |(42788143/80000000 : ℝ)|=(42788143/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311348399/2500000000 : ℝ)|^4329 ≤ (2684330199523/6250000000000 : ℝ)^3305
        have hw : |(1311348399/2500000000 : ℝ)|=(1311348399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-131586981/625000000 : ℝ)|^4329 ≤ (3248020206053/25000000000000 : ℝ)^3305
        have hw : |(-131586981/625000000 : ℝ)|=(131586981/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s6_3 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1079901867/2500000000 : ℝ)*x 0 + (2073680723/5000000000 : ℝ)*x 1 + (4498442027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079901867/2500000000 : ℝ)^4329 ≤ (33303714782377/100000000000000 : ℝ)^3305 := by
    have hnat : (1079901867 : ℕ)^4329*100000000000000^3305 ≤ 33303714782377^3305*2500000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079901867 2500000000 33303714782377 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2073680723/5000000000 : ℝ)^4329 ≤ (31575103234489/100000000000000 : ℝ)^3305 := by
    have hnat : (2073680723 : ℕ)^4329*100000000000000^3305 ≤ 31575103234489^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073680723 5000000000 31575103234489 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4498442027/10000000000 : ℝ)^4329 ≤ (35121181958827/100000000000000 : ℝ)^3305 := by
    have hnat : (4498442027 : ℕ)^4329*100000000000000^3305 ≤ 35121181958827^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498442027 10000000000 35121181958827 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079901867/2500000000 : ℝ), (2073680723/5000000000 : ℝ), (4498442027/10000000000 : ℝ)] ![(33303714782377/100000000000000 : ℝ), (31575103234489/100000000000000 : ℝ), (35121181958827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079901867/2500000000 : ℝ)|^4329 ≤ (33303714782377/100000000000000 : ℝ)^3305
        have hw : |(1079901867/2500000000 : ℝ)|=(1079901867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2073680723/5000000000 : ℝ)|^4329 ≤ (31575103234489/100000000000000 : ℝ)^3305
        have hw : |(2073680723/5000000000 : ℝ)|=(2073680723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4498442027/10000000000 : ℝ)|^4329 ≤ (35121181958827/100000000000000 : ℝ)^3305
        have hw : |(4498442027/10000000000 : ℝ)|=(4498442027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s6_4 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2020882803/10000000000 : ℝ)*x 0 + (2622994641/5000000000 : ℝ)*x 1 + (676340433/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2020882803/10000000000 : ℝ)^4329 ≤ (6156649791609/50000000000000 : ℝ)^3305 := by
    have hnat : (2020882803 : ℕ)^4329*50000000000000^3305 ≤ 6156649791609^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2020882803 10000000000 6156649791609 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622994641/5000000000 : ℝ)^4329 ≤ (4295567198797/10000000000000 : ℝ)^3305 := by
    have hnat : (2622994641 : ℕ)^4329*10000000000000^3305 ≤ 4295567198797^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622994641 5000000000 4295567198797 10000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676340433/1250000000 : ℝ)^4329 ≤ (44731028418423/100000000000000 : ℝ)^3305 := by
    have hnat : (676340433 : ℕ)^4329*100000000000000^3305 ≤ 44731028418423^3305*1250000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676340433 1250000000 44731028418423 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2020882803/10000000000 : ℝ), (2622994641/5000000000 : ℝ), (676340433/1250000000 : ℝ)] ![(6156649791609/50000000000000 : ℝ), (4295567198797/10000000000000 : ℝ), (44731028418423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2020882803/10000000000 : ℝ)|^4329 ≤ (6156649791609/50000000000000 : ℝ)^3305
        have hw : |(-2020882803/10000000000 : ℝ)|=(2020882803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622994641/5000000000 : ℝ)|^4329 ≤ (4295567198797/10000000000000 : ℝ)^3305
        have hw : |(2622994641/5000000000 : ℝ)|=(2622994641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676340433/1250000000 : ℝ)|^4329 ≤ (44731028418423/100000000000000 : ℝ)^3305
        have hw : |(676340433/1250000000 : ℝ)|=(676340433/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s6_5 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (16580151/31250000 : ℝ)*x 0 + (-1940062041/10000000000 : ℝ)*x 1 + (5410723467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16580151/31250000 : ℝ)^4329 ≤ (8719331421757/20000000000000 : ℝ)^3305 := by
    have hnat : (16580151 : ℕ)^4329*20000000000000^3305 ≤ 8719331421757^3305*31250000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16580151 31250000 8719331421757 20000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1940062041/10000000000 : ℝ)^4329 ≤ (1459039303137/12500000000000 : ℝ)^3305 := by
    have hnat : (1940062041 : ℕ)^4329*12500000000000^3305 ≤ 1459039303137^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1940062041 10000000000 1459039303137 12500000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410723467/10000000000 : ℝ)^4329 ≤ (11182757112727/25000000000000 : ℝ)^3305 := by
    have hnat : (5410723467 : ℕ)^4329*25000000000000^3305 ≤ 11182757112727^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410723467 10000000000 11182757112727 25000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16580151/31250000 : ℝ), (-1940062041/10000000000 : ℝ), (5410723467/10000000000 : ℝ)] ![(8719331421757/20000000000000 : ℝ), (1459039303137/12500000000000 : ℝ), (11182757112727/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16580151/31250000 : ℝ)|^4329 ≤ (8719331421757/20000000000000 : ℝ)^3305
        have hw : |(16580151/31250000 : ℝ)|=(16580151/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1940062041/10000000000 : ℝ)|^4329 ≤ (1459039303137/12500000000000 : ℝ)^3305
        have hw : |(-1940062041/10000000000 : ℝ)|=(1940062041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410723467/10000000000 : ℝ)|^4329 ≤ (11182757112727/25000000000000 : ℝ)^3305
        have hw : |(5410723467/10000000000 : ℝ)|=(5410723467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s6_6 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652824161/5000000000 : ℝ)*x 0 + (2705361733/5000000000 : ℝ)*x 1 + (-48501551/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652824161/5000000000 : ℝ)^4329 ≤ (4359665713031/10000000000000 : ℝ)^3305 := by
    have hnat : (2652824161 : ℕ)^4329*10000000000000^3305 ≤ 4359665713031^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652824161 5000000000 4359665713031 10000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705361733/5000000000 : ℝ)^4329 ≤ (559137855501/1250000000000 : ℝ)^3305 := by
    have hnat : (2705361733 : ℕ)^4329*1250000000000^3305 ≤ 559137855501^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705361733 5000000000 559137855501 1250000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (48501551/250000000 : ℝ)^4329 ≤ (2334462883443/20000000000000 : ℝ)^3305 := by
    have hnat : (48501551 : ℕ)^4329*20000000000000^3305 ≤ 2334462883443^3305*250000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48501551 250000000 2334462883443 20000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652824161/5000000000 : ℝ), (2705361733/5000000000 : ℝ), (-48501551/250000000 : ℝ)] ![(4359665713031/10000000000000 : ℝ), (559137855501/1250000000000 : ℝ), (2334462883443/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652824161/5000000000 : ℝ)|^4329 ≤ (4359665713031/10000000000000 : ℝ)^3305
        have hw : |(2652824161/5000000000 : ℝ)|=(2652824161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705361733/5000000000 : ℝ)|^4329 ≤ (559137855501/1250000000000 : ℝ)^3305
        have hw : |(2705361733/5000000000 : ℝ)|=(2705361733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-48501551/250000000 : ℝ)|^4329 ≤ (2334462883443/20000000000000 : ℝ)^3305
        have hw : |(-48501551/250000000 : ℝ)|=(48501551/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s6_7 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2159816493/5000000000 : ℝ)*x 0 + (4497182857/10000000000 : ℝ)*x 1 + (1037156691/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2159816493/5000000000 : ℝ)^4329 ≤ (16651986240337/50000000000000 : ℝ)^3305 := by
    have hnat : (2159816493 : ℕ)^4329*50000000000000^3305 ≤ 16651986240337^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159816493 5000000000 16651986240337 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4497182857/10000000000 : ℝ)^4329 ≤ (7021661146207/20000000000000 : ℝ)^3305 := by
    have hnat : (4497182857 : ℕ)^4329*20000000000000^3305 ≤ 7021661146207^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497182857 10000000000 7021661146207 20000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1037156691/2500000000 : ℝ)^4329 ≤ (7896930444471/25000000000000 : ℝ)^3305 := by
    have hnat : (1037156691 : ℕ)^4329*25000000000000^3305 ≤ 7896930444471^3305*2500000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037156691 2500000000 7896930444471 25000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2159816493/5000000000 : ℝ), (4497182857/10000000000 : ℝ), (1037156691/2500000000 : ℝ)] ![(16651986240337/50000000000000 : ℝ), (7021661146207/20000000000000 : ℝ), (7896930444471/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2159816493/5000000000 : ℝ)|^4329 ≤ (16651986240337/50000000000000 : ℝ)^3305
        have hw : |(2159816493/5000000000 : ℝ)|=(2159816493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4497182857/10000000000 : ℝ)|^4329 ≤ (7021661146207/20000000000000 : ℝ)^3305
        have hw : |(4497182857/10000000000 : ℝ)|=(4497182857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1037156691/2500000000 : ℝ)|^4329 ≤ (7896930444471/25000000000000 : ℝ)^3305
        have hw : |(1037156691/2500000000 : ℝ)|=(1037156691/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1369_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77896747/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1473/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2241/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11211/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3681/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1473/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2241/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1473/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2241/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1473/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2241/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1473/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2241/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1473/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2241/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1473/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2241/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2241/20000 : ℝ) ^ (541/128 : ℝ) ≤ (4800094887780383/50000000000000000000 : ℝ) := by
    have hpowers : (2241/20000 : ℝ)^541 ≤ (4800094887780383/50000000000000000000 : ℝ)^128 := by
      have hnat : (2241 : ℕ)^541*50000000000000000000^128 ≤ 4800094887780383^128*20000^541 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2241 20000 4800094887780383 50000000000000000000 541 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2241/20000 : ℝ)) (X := (4800094887780383/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have hpowhi : (1473/10000 : ℝ) ^ (541/128 : ℝ) ≤ (7626002281621121/25000000000000000000 : ℝ) := by
    have hpowers : (1473/10000 : ℝ)^541 ≤ (7626002281621121/25000000000000000000 : ℝ)^128 := by
      have hnat : (1473 : ℕ)^541*25000000000000000000^128 ≤ 7626002281621121^128*10000^541 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1473 10000 7626002281621121 25000000000000000000 541 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1473/10000 : ℝ)) (X := (7626002281621121/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004800094887780383/25000000000000000000 : ℝ) ≤ (10000454245561337/10000000000000000 : ℝ) ^ (541/128 : ℝ) := by
    have hpowers : (25004800094887780383/25000000000000000000 : ℝ)^128 ≤ (10000454245561337/10000000000000000 : ℝ)^541 := by
      have hnat : (25004800094887780383 : ℕ)^128*10000000000000000^541 ≤ 10000454245561337^541*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004800094887780383 25000000000000000000 10000454245561337 10000000000000000 128 541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000454245561337/10000000000000000 : ℝ)) (X := (25004800094887780383/25000000000000000000 : ℝ)) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (400160416795608181/400000000000000000 : ℝ) ≤ (10000948715682787/10000000000000000 : ℝ) ^ (541/128 : ℝ) := by
    have hpowers : (400160416795608181/400000000000000000 : ℝ)^128 ≤ (10000948715682787/10000000000000000 : ℝ)^541 := by
      have hnat : (400160416795608181 : ℕ)^128*10000000000000000^541 ≤ 10000948715682787^541*400000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        400160416795608181 400000000000000000 10000948715682787 10000000000000000 128 541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000948715682787/10000000000000000 : ℝ)) (X := (400160416795608181/400000000000000000 : ℝ)) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507626002281621121/12500000000000000000 : ℝ) ≤ (10001443185804237/10000000000000000 : ℝ) ^ (541/128 : ℝ) := by
    have hpowers : (12507626002281621121/12500000000000000000 : ℝ)^128 ≤ (10001443185804237/10000000000000000 : ℝ)^541 := by
      have hnat : (12507626002281621121 : ℕ)^128*10000000000000000^541 ≤ 10001443185804237^541*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507626002281621121 12500000000000000000 10001443185804237 10000000000000000 128 541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001443185804237/10000000000000000 : ℝ)) (X := (12507626002281621121/12500000000000000000 : ℝ)) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4800094887780383/50000000000000000000 : ℝ) ≤ ((469873601869093579/470000000000000000 : ℝ)+2*(9889402429/7050000000000 : ℝ)*(2241/20000 : ℝ))^(541/128 : ℝ) := by
    rw [show (469873601869093579/470000000000000000 : ℝ)+2*(9889402429/7050000000000 : ℝ)*(2241/20000 : ℝ)=(10000454245561337/10000000000000000 : ℝ) by norm_num, show 1+2*(4800094887780383/50000000000000000000 : ℝ)=(25004800094887780383/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7626002281621121/25000000000000000000 : ℝ)+(4800094887780383/50000000000000000000 : ℝ) ≤ ((469873601869093579/470000000000000000 : ℝ)+(9889402429/7050000000000 : ℝ)*((1473/10000 : ℝ)+(2241/20000 : ℝ)))^(541/128 : ℝ) := by
    rw [show (469873601869093579/470000000000000000 : ℝ)+(9889402429/7050000000000 : ℝ)*((1473/10000 : ℝ)+(2241/20000 : ℝ))=(10000948715682787/10000000000000000 : ℝ) by norm_num, show 1+(7626002281621121/25000000000000000000 : ℝ)+(4800094887780383/50000000000000000000 : ℝ)=(400160416795608181/400000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7626002281621121/25000000000000000000 : ℝ) ≤ ((469873601869093579/470000000000000000 : ℝ)+2*(9889402429/7050000000000 : ℝ)*(1473/10000 : ℝ))^(541/128 : ℝ) := by
    rw [show (469873601869093579/470000000000000000 : ℝ)+2*(9889402429/7050000000000 : ℝ)*(1473/10000 : ℝ)=(10001443185804237/10000000000000000 : ℝ) by norm_num, show 1+2*(7626002281621121/25000000000000000000 : ℝ)=(12507626002281621121/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (469873601869093579/470000000000000000 : ℝ)*(X 1 0+X 2 0)+(9889402429/7050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (541/128 : ℝ)) (lo := (2241/20000 : ℝ)) (hi := (1473/10000 : ℝ)) (c := (469873601869093579/470000000000000000 : ℝ)) (alpha := (9889402429/7050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (469873601869093579/470000000000000000 : ℝ)*(X 0 1+X 2 1)+(9889402429/7050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (541/128 : ℝ)) (lo := (2241/20000 : ℝ)) (hi := (1473/10000 : ℝ)) (c := (469873601869093579/470000000000000000 : ℝ)) (alpha := (9889402429/7050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (469873601869093579/470000000000000000 : ℝ)*(X 0 2+X 1 2)+(9889402429/7050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (541/128 : ℝ)) (lo := (2241/20000 : ℝ)) (hi := (1473/10000 : ℝ)) (c := (469873601869093579/470000000000000000 : ℝ)) (alpha := (9889402429/7050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-404174249/2000000000 : ℝ)*X 0 0+(541132261/1000000000 : ℝ)*X 0 1+(1311348237/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674258989/5000000000 : ℝ)*X 1 0+(-2105391641/10000000000 : ℝ)*X 1 1+(1049078707/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((42788143/80000000 : ℝ)*X 2 0+(1311348399/2500000000 : ℝ)*X 2 1+(-131586981/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1079901867/2500000000 : ℝ)*X 0 0+(2073680723/5000000000 : ℝ)*X 0 1+(4498442027/10000000000 : ℝ)*X 0 2+(1079901867/2500000000 : ℝ)*X 1 0+(2073680723/5000000000 : ℝ)*X 1 1+(4498442027/10000000000 : ℝ)*X 1 2+(1079901867/2500000000 : ℝ)*X 2 0+(2073680723/5000000000 : ℝ)*X 2 1+(4498442027/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2020882803/10000000000 : ℝ)*X 0 0+(2622994641/5000000000 : ℝ)*X 0 1+(676340433/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((16580151/31250000 : ℝ)*X 1 0+(-1940062041/10000000000 : ℝ)*X 1 1+(5410723467/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652824161/5000000000 : ℝ)*X 2 0+(2705361733/5000000000 : ℝ)*X 2 1+(-48501551/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2159816493/5000000000 : ℝ)*X 0 0+(4497182857/10000000000 : ℝ)*X 0 1+(1037156691/2500000000 : ℝ)*X 0 2+(2159816493/5000000000 : ℝ)*X 1 0+(4497182857/10000000000 : ℝ)*X 1 1+(1037156691/2500000000 : ℝ)*X 1 2+(2159816493/5000000000 : ℝ)*X 2 0+(4497182857/10000000000 : ℝ)*X 2 1+(1037156691/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (162386320467770146821/58750000000000000000000000 : ℝ) := by norm_num
    linear_combination (1621722199/100000000000000 : ℝ)*(base19) + (65050959/5000000000000 : ℝ)*(base23) + (87143187/100000000000000 : ℝ)*(upper2) + (29357297/12500000000000 : ℝ)*(upper3) + (12287257/6250000000000 : ℝ)*(upper4) + (4437563562830609/100000000000000 : ℝ)*(major0) + (4437563562830609/100000000000000 : ℝ)*(major1) + (4437563562830609/100000000000000 : ℝ)*(major2) + (3013355318823929/50000000000000 : ℝ)*(sp0) + (3013381423072193/50000000000000 : ℝ)*(sp1) + (1205352633369481/20000000000000 : ℝ)*(sp2) + (284835380917691/10000000000000 : ℝ)*(sp3) + (53830218727/100000000000000 : ℝ)*(sp4) + (2189120909/25000000000000 : ℝ)*(sp7) + (1424181282830273/50000000000000 : ℝ)*(f.failure) + (1205352893573317/20000000000000 : ℝ)*(f.sum) + (1853294679097/705000000000000000000000000 : ℝ)*base65 + (1018298463254121167/141000000000000000000000000000000 : ℝ)*base68 + (3182680665878833/141000000000000000000000000000000 : ℝ)*base69 + (689358292647878833/141000000000000000000000000000000 : ℝ)*base71 + (715171436473/176250000000000000000000000 : ℝ)*base73 + (579967320147878833/141000000000000000000000000000000 : ℝ)*base75 + (232089801599121167/141000000000000000000000000000000 : ℝ)*base78 + (584732626280121167/141000000000000000000000000000000 : ℝ)*base80 + (122678617961/22031250000000000000000000 : ℝ)*base81 + (5178069/2500000000000000000000 : ℝ)*base90 + (5178069/2500000000000000000000 : ℝ)*base92 + (5178069/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1529895533292099607299/235000000000000000000000000 : ℝ) := by norm_num
    linear_combination (562179257/50000000000000 : ℝ)*(base19) + (244906379/20000000000000 : ℝ)*(base23) + (134240163/100000000000000 : ℝ)*(upper3) + (22127963/50000000000000 : ℝ)*(lower4) + (16958953/12500000000000 : ℝ)*(upper5) + (2234840818816779/50000000000000 : ℝ)*(major0) + (2234840818816779/50000000000000 : ℝ)*(major1) + (2234840818816779/50000000000000 : ℝ)*(major2) + (23200890711/100000000000000 : ℝ)*(sp1) + (2499207213/10000000000000 : ℝ)*(sp2) + (6070384692813913/100000000000000 : ℝ)*(sp4) + (6070360367564687/100000000000000 : ℝ)*(sp5) + (189698702381559/3125000000000 : ℝ)*(sp6) + (179311147840421/6250000000000 : ℝ)*(sp7) + (179311147840421/6250000000000 : ℝ)*(f.failure) + (6070384692813913/100000000000000 : ℝ)*(f.sum) + (658027785693/235000000000000000000000000 : ℝ)*base65 + (49609021537237959/23500000000000000000000000000000 : ℝ)*base68 + (96877953089762041/23500000000000000000000000000000 : ℝ)*base69 + (215566701576762041/23500000000000000000000000000000 : ℝ)*base71 + (815473269701/117500000000000000000000000 : ℝ)*base74 + (612524151412762041/23500000000000000000000000000000 : ℝ)*base75 + (73759505391237959/23500000000000000000000000000000 : ℝ)*base78 + (171725145854237959/23500000000000000000000000000000 : ℝ)*base80 + (286620364963/58750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (2260487/312500000000000000000 : ℝ)*base89 + (2260487/312500000000000000000 : ℝ)*base91 + (2260487/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1369_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77896747/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1473/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2241/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11211/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3681/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1369_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1369_s7_0 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-202087551/1000000000 : ℝ)*x 0 + (5411274453/10000000000 : ℝ)*x 1 + (2622719199/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (202087551/1000000000 : ℝ)^4329 ≤ (12313241378873/100000000000000 : ℝ)^3305 := by
    have hnat : (202087551 : ℕ)^4329*100000000000000^3305 ≤ 12313241378873^3305*1000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202087551 1000000000 12313241378873 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411274453/10000000000 : ℝ)^4329 ≤ (44736994915699/100000000000000 : ℝ)^3305 := by
    have hnat : (5411274453 : ℕ)^4329*100000000000000^3305 ≤ 44736994915699^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411274453 10000000000 44736994915699 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622719199/5000000000 : ℝ)^4329 ≤ (21474881845379/50000000000000 : ℝ)^3305 := by
    have hnat : (2622719199 : ℕ)^4329*50000000000000^3305 ≤ 21474881845379^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622719199 5000000000 21474881845379 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-202087551/1000000000 : ℝ), (5411274453/10000000000 : ℝ), (2622719199/5000000000 : ℝ)] ![(12313241378873/100000000000000 : ℝ), (44736994915699/100000000000000 : ℝ), (21474881845379/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-202087551/1000000000 : ℝ)|^4329 ≤ (12313241378873/100000000000000 : ℝ)^3305
        have hw : |(-202087551/1000000000 : ℝ)|=(202087551/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411274453/10000000000 : ℝ)|^4329 ≤ (44736994915699/100000000000000 : ℝ)^3305
        have hw : |(5411274453/10000000000 : ℝ)|=(5411274453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622719199/5000000000 : ℝ)|^4329 ≤ (21474881845379/50000000000000 : ℝ)^3305
        have hw : |(2622719199/5000000000 : ℝ)|=(2622719199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s7_1 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267425283/500000000 : ℝ)*x 0 + (-2105348499/10000000000 : ℝ)*x 1 + (5245438441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267425283/500000000 : ℝ)^4329 ≤ (44058504167323/100000000000000 : ℝ)^3305 := by
    have hnat : (267425283 : ℕ)^4329*100000000000000^3305 ≤ 44058504167323^3305*500000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267425283 500000000 44058504167323 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2105348499/10000000000 : ℝ)^4329 ≤ (3247932918133/25000000000000 : ℝ)^3305 := by
    have hnat : (2105348499 : ℕ)^4329*25000000000000^3305 ≤ 3247932918133^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105348499 10000000000 3247932918133 25000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245438441/10000000000 : ℝ)^4329 ≤ (42949764151931/100000000000000 : ℝ)^3305 := by
    have hnat : (5245438441 : ℕ)^4329*100000000000000^3305 ≤ 42949764151931^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245438441 10000000000 42949764151931 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267425283/500000000 : ℝ), (-2105348499/10000000000 : ℝ), (5245438441/10000000000 : ℝ)] ![(44058504167323/100000000000000 : ℝ), (3247932918133/25000000000000 : ℝ), (42949764151931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267425283/500000000 : ℝ)|^4329 ≤ (44058504167323/100000000000000 : ℝ)^3305
        have hw : |(267425283/500000000 : ℝ)|=(267425283/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2105348499/10000000000 : ℝ)|^4329 ≤ (3247932918133/25000000000000 : ℝ)^3305
        have hw : |(-2105348499/10000000000 : ℝ)|=(2105348499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245438441/10000000000 : ℝ)|^4329 ≤ (42949764151931/100000000000000 : ℝ)^3305
        have hw : |(5245438441/10000000000 : ℝ)|=(5245438441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s7_2 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337126423/2500000000 : ℝ)*x 0 + (209817537/400000000 : ℝ)*x 1 + (-1052674239/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337126423/2500000000 : ℝ)^4329 ≤ (11014626128149/25000000000000 : ℝ)^3305 := by
    have hnat : (1337126423 : ℕ)^4329*25000000000000^3305 ≤ 11014626128149^3305*2500000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337126423 2500000000 11014626128149 25000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209817537/400000000 : ℝ)^4329 ≤ (10737440995083/25000000000000 : ℝ)^3305 := by
    have hnat : (209817537 : ℕ)^4329*25000000000000^3305 ≤ 10737440995083^3305*400000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209817537 400000000 10737440995083 25000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052674239/5000000000 : ℝ)^4329 ≤ (6495865751397/50000000000000 : ℝ)^3305 := by
    have hnat : (1052674239 : ℕ)^4329*50000000000000^3305 ≤ 6495865751397^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052674239 5000000000 6495865751397 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337126423/2500000000 : ℝ), (209817537/400000000 : ℝ), (-1052674239/5000000000 : ℝ)] ![(11014626128149/25000000000000 : ℝ), (10737440995083/25000000000000 : ℝ), (6495865751397/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337126423/2500000000 : ℝ)|^4329 ≤ (11014626128149/25000000000000 : ℝ)^3305
        have hw : |(1337126423/2500000000 : ℝ)|=(1337126423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209817537/400000000 : ℝ)|^4329 ≤ (10737440995083/25000000000000 : ℝ)^3305
        have hw : |(209817537/400000000 : ℝ)|=(209817537/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1052674239/5000000000 : ℝ)|^4329 ≤ (6495865751397/50000000000000 : ℝ)^3305
        have hw : |(-1052674239/5000000000 : ℝ)|=(1052674239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s7_3 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (863922217/2000000000 : ℝ)*x 0 + (4147457429/10000000000 : ℝ)*x 1 + (2249172429/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (863922217/2000000000 : ℝ)^4329 ≤ (33303751309299/100000000000000 : ℝ)^3305 := by
    have hnat : (863922217 : ℕ)^4329*100000000000000^3305 ≤ 33303751309299^3305*2000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863922217 2000000000 33303751309299 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4147457429/10000000000 : ℝ)^4329 ≤ (15788030197631/50000000000000 : ℝ)^3305 := by
    have hnat : (4147457429 : ℕ)^4329*50000000000000^3305 ≤ 15788030197631^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4147457429 10000000000 15788030197631 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2249172429/5000000000 : ℝ)^4329 ≤ (3512018827231/10000000000000 : ℝ)^3305 := by
    have hnat : (2249172429 : ℕ)^4329*10000000000000^3305 ≤ 3512018827231^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249172429 5000000000 3512018827231 10000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(863922217/2000000000 : ℝ), (4147457429/10000000000 : ℝ), (2249172429/5000000000 : ℝ)] ![(33303751309299/100000000000000 : ℝ), (15788030197631/50000000000000 : ℝ), (3512018827231/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(863922217/2000000000 : ℝ)|^4329 ≤ (33303751309299/100000000000000 : ℝ)^3305
        have hw : |(863922217/2000000000 : ℝ)|=(863922217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4147457429/10000000000 : ℝ)|^4329 ≤ (15788030197631/50000000000000 : ℝ)^3305
        have hw : |(4147457429/10000000000 : ℝ)|=(4147457429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2249172429/5000000000 : ℝ)|^4329 ≤ (3512018827231/10000000000000 : ℝ)^3305
        have hw : |(2249172429/5000000000 : ℝ)|=(2249172429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s7_4 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2020887371/10000000000 : ℝ)*x 0 + (5246033109/10000000000 : ℝ)*x 1 + (338167293/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2020887371/10000000000 : ℝ)^4329 ≤ (6156668019889/50000000000000 : ℝ)^3305 := by
    have hnat : (2020887371 : ℕ)^4329*50000000000000^3305 ≤ 6156668019889^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2020887371 10000000000 6156668019889 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246033109/10000000000 : ℝ)^4329 ≤ (10739035511519/25000000000000 : ℝ)^3305 := by
    have hnat : (5246033109 : ℕ)^4329*25000000000000^3305 ≤ 10739035511519^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246033109 10000000000 10739035511519 25000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338167293/625000000 : ℝ)^4329 ≤ (5591315237949/12500000000000 : ℝ)^3305 := by
    have hnat : (338167293 : ℕ)^4329*12500000000000^3305 ≤ 5591315237949^3305*625000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338167293 625000000 5591315237949 12500000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2020887371/10000000000 : ℝ), (5246033109/10000000000 : ℝ), (338167293/625000000 : ℝ)] ![(6156668019889/50000000000000 : ℝ), (10739035511519/25000000000000 : ℝ), (5591315237949/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2020887371/10000000000 : ℝ)|^4329 ≤ (6156668019889/50000000000000 : ℝ)^3305
        have hw : |(-2020887371/10000000000 : ℝ)|=(2020887371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246033109/10000000000 : ℝ)|^4329 ≤ (10739035511519/25000000000000 : ℝ)^3305
        have hw : |(5246033109/10000000000 : ℝ)|=(5246033109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338167293/625000000 : ℝ)|^4329 ≤ (5591315237949/12500000000000 : ℝ)^3305
        have hw : |(338167293/625000000 : ℝ)|=(338167293/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s7_5 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305660163/10000000000 : ℝ)*x 0 + (-970055151/5000000000 : ℝ)*x 1 + (5410676573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305660163/10000000000 : ℝ)^4329 ≤ (43596784574307/100000000000000 : ℝ)^3305 := by
    have hnat : (5305660163 : ℕ)^4329*100000000000000^3305 ≤ 43596784574307^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305660163 10000000000 43596784574307 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (970055151/5000000000 : ℝ)^4329 ≤ (11672694750619/100000000000000 : ℝ)^3305 := by
    have hnat : (970055151 : ℕ)^4329*100000000000000^3305 ≤ 11672694750619^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      970055151 5000000000 11672694750619 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410676573/10000000000 : ℝ)^4329 ≤ (22365260329157/50000000000000 : ℝ)^3305 := by
    have hnat : (5410676573 : ℕ)^4329*50000000000000^3305 ≤ 22365260329157^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410676573 10000000000 22365260329157 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305660163/10000000000 : ℝ), (-970055151/5000000000 : ℝ), (5410676573/10000000000 : ℝ)] ![(43596784574307/100000000000000 : ℝ), (11672694750619/100000000000000 : ℝ), (22365260329157/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305660163/10000000000 : ℝ)|^4329 ≤ (43596784574307/100000000000000 : ℝ)^3305
        have hw : |(5305660163/10000000000 : ℝ)|=(5305660163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-970055151/5000000000 : ℝ)|^4329 ≤ (11672694750619/100000000000000 : ℝ)^3305
        have hw : |(-970055151/5000000000 : ℝ)|=(970055151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410676573/10000000000 : ℝ)|^4329 ≤ (22365260329157/50000000000000 : ℝ)^3305
        have hw : |(5410676573/10000000000 : ℝ)|=(5410676573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s7_6 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305660047/10000000000 : ℝ)*x 0 + (541067677/1000000000 : ℝ)*x 1 + (-194011019/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305660047/10000000000 : ℝ)^4329 ≤ (21798391662903/50000000000000 : ℝ)^3305 := by
    have hnat : (5305660047 : ℕ)^4329*50000000000000^3305 ≤ 21798391662903^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305660047 10000000000 21798391662903 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541067677/1000000000 : ℝ)^4329 ≤ (44730522791529/100000000000000 : ℝ)^3305 := by
    have hnat : (541067677 : ℕ)^4329*100000000000000^3305 ≤ 44730522791529^3305*1000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541067677 1000000000 44730522791529 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (194011019/1000000000 : ℝ)^4329 ≤ (11672693867989/100000000000000 : ℝ)^3305 := by
    have hnat : (194011019 : ℕ)^4329*100000000000000^3305 ≤ 11672693867989^3305*1000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194011019 1000000000 11672693867989 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305660047/10000000000 : ℝ), (541067677/1000000000 : ℝ), (-194011019/1000000000 : ℝ)] ![(21798391662903/50000000000000 : ℝ), (44730522791529/100000000000000 : ℝ), (11672693867989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305660047/10000000000 : ℝ)|^4329 ≤ (21798391662903/50000000000000 : ℝ)^3305
        have hw : |(5305660047/10000000000 : ℝ)|=(5305660047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541067677/1000000000 : ℝ)|^4329 ≤ (44730522791529/100000000000000 : ℝ)^3305
        have hw : |(541067677/1000000000 : ℝ)|=(541067677/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-194011019/1000000000 : ℝ)|^4329 ≤ (11672693867989/100000000000000 : ℝ)^3305
        have hw : |(-194011019/1000000000 : ℝ)|=(194011019/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s7_7 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2159818069/5000000000 : ℝ)*x 0 + (4497086453/10000000000 : ℝ)*x 1 + (829744483/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2159818069/5000000000 : ℝ)^4329 ≤ (4163000538971/12500000000000 : ℝ)^3305 := by
    have hnat : (2159818069 : ℕ)^4329*12500000000000^3305 ≤ 4163000538971^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159818069 5000000000 4163000538971 12500000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4497086453/10000000000 : ℝ)^4329 ≤ (35107319953177/100000000000000 : ℝ)^3305 := by
    have hnat : (4497086453 : ℕ)^4329*100000000000000^3305 ≤ 35107319953177^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497086453 10000000000 35107319953177 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (829744483/2000000000 : ℝ)^4329 ≤ (1974292232377/6250000000000 : ℝ)^3305 := by
    have hnat : (829744483 : ℕ)^4329*6250000000000^3305 ≤ 1974292232377^3305*2000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      829744483 2000000000 1974292232377 6250000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2159818069/5000000000 : ℝ), (4497086453/10000000000 : ℝ), (829744483/2000000000 : ℝ)] ![(4163000538971/12500000000000 : ℝ), (35107319953177/100000000000000 : ℝ), (1974292232377/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2159818069/5000000000 : ℝ)|^4329 ≤ (4163000538971/12500000000000 : ℝ)^3305
        have hw : |(2159818069/5000000000 : ℝ)|=(2159818069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4497086453/10000000000 : ℝ)|^4329 ≤ (35107319953177/100000000000000 : ℝ)^3305
        have hw : |(4497086453/10000000000 : ℝ)|=(4497086453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(829744483/2000000000 : ℝ)|^4329 ≤ (1974292232377/6250000000000 : ℝ)^3305
        have hw : |(829744483/2000000000 : ℝ)|=(829744483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1369_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77896747/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3681/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11211/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2803/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14723/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3681/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11211/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3681/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11211/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3681/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11211/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3681/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11211/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3681/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11211/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3681/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11211/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11211/100000 : ℝ) ^ (541/128 : ℝ) ≤ (4810967944898659/50000000000000000000 : ℝ) := by
    have hpowers : (11211/100000 : ℝ)^541 ≤ (4810967944898659/50000000000000000000 : ℝ)^128 := by
      have hnat : (11211 : ℕ)^541*50000000000000000000^128 ≤ 4810967944898659^128*100000^541 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11211 100000 4810967944898659 50000000000000000000 541 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11211/100000 : ℝ)) (X := (4810967944898659/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have hpowhi : (3681/25000 : ℝ) ^ (541/128 : ℝ) ≤ (609030549915477/2000000000000000000 : ℝ) := by
    have hpowers : (3681/25000 : ℝ)^541 ≤ (609030549915477/2000000000000000000 : ℝ)^128 := by
      have hnat : (3681 : ℕ)^541*2000000000000000000^128 ≤ 609030549915477^128*25000^541 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3681 25000 609030549915477 2000000000000000000 541 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3681/25000 : ℝ)) (X := (609030549915477/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004810967944898659/25000000000000000000 : ℝ) ≤ (625028454651979/625000000000000 : ℝ) ^ (541/128 : ℝ) := by
    have hpowers : (25004810967944898659/25000000000000000000 : ℝ)^128 ≤ (625028454651979/625000000000000 : ℝ)^541 := by
      have hnat : (25004810967944898659 : ℕ)^128*625000000000000^541 ≤ 625028454651979^541*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004810967944898659 25000000000000000000 625028454651979 625000000000000 128 541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625028454651979/625000000000000 : ℝ)) (X := (25004810967944898659/25000000000000000000 : ℝ)) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126252295730799099/3125000000000000000 : ℝ) ≤ (10000947988706349/10000000000000000 : ℝ) ^ (541/128 : ℝ) := by
    have hpowers : (3126252295730799099/3125000000000000000 : ℝ)^128 ≤ (10000947988706349/10000000000000000 : ℝ)^541 := by
      have hnat : (3126252295730799099 : ℕ)^128*10000000000000000^541 ≤ 10000947988706349^541*3125000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126252295730799099 3125000000000000000 10000947988706349 10000000000000000 128 541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000947988706349/10000000000000000 : ℝ)) (X := (3126252295730799099/3125000000000000000 : ℝ)) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (1000609030549915477/1000000000000000000 : ℝ) ≤ (5000720351490517/5000000000000000 : ℝ) ^ (541/128 : ℝ) := by
    have hpowers : (1000609030549915477/1000000000000000000 : ℝ)^128 ≤ (5000720351490517/5000000000000000 : ℝ)^541 := by
      have hnat : (1000609030549915477 : ℕ)^128*5000000000000000^541 ≤ 5000720351490517^541*1000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000609030549915477 1000000000000000000 5000720351490517 5000000000000000 128 541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000720351490517/5000000000000000 : ℝ)) (X := (1000609030549915477/1000000000000000000 : ℝ)) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4810967944898659/50000000000000000000 : ℝ) ≤ ((5853425289935241427/5855000000000000000 : ℝ)+2*(98542854937/70260000000000 : ℝ)*(11211/100000 : ℝ))^(541/128 : ℝ) := by
    rw [show (5853425289935241427/5855000000000000000 : ℝ)+2*(98542854937/70260000000000 : ℝ)*(11211/100000 : ℝ)=(625028454651979/625000000000000 : ℝ) by norm_num, show 1+2*(4810967944898659/50000000000000000000 : ℝ)=(25004810967944898659/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(609030549915477/2000000000000000000 : ℝ)+(4810967944898659/50000000000000000000 : ℝ) ≤ ((5853425289935241427/5855000000000000000 : ℝ)+(98542854937/70260000000000 : ℝ)*((3681/25000 : ℝ)+(11211/100000 : ℝ)))^(541/128 : ℝ) := by
    rw [show (5853425289935241427/5855000000000000000 : ℝ)+(98542854937/70260000000000 : ℝ)*((3681/25000 : ℝ)+(11211/100000 : ℝ))=(10000947988706349/10000000000000000 : ℝ) by norm_num, show 1+(609030549915477/2000000000000000000 : ℝ)+(4810967944898659/50000000000000000000 : ℝ)=(3126252295730799099/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(609030549915477/2000000000000000000 : ℝ) ≤ ((5853425289935241427/5855000000000000000 : ℝ)+2*(98542854937/70260000000000 : ℝ)*(3681/25000 : ℝ))^(541/128 : ℝ) := by
    rw [show (5853425289935241427/5855000000000000000 : ℝ)+2*(98542854937/70260000000000 : ℝ)*(3681/25000 : ℝ)=(5000720351490517/5000000000000000 : ℝ) by norm_num, show 1+2*(609030549915477/2000000000000000000 : ℝ)=(1000609030549915477/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5853425289935241427/5855000000000000000 : ℝ)*(X 1 0+X 2 0)+(98542854937/70260000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (541/128 : ℝ)) (lo := (11211/100000 : ℝ)) (hi := (3681/25000 : ℝ)) (c := (5853425289935241427/5855000000000000000 : ℝ)) (alpha := (98542854937/70260000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5853425289935241427/5855000000000000000 : ℝ)*(X 0 1+X 2 1)+(98542854937/70260000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (541/128 : ℝ)) (lo := (11211/100000 : ℝ)) (hi := (3681/25000 : ℝ)) (c := (5853425289935241427/5855000000000000000 : ℝ)) (alpha := (98542854937/70260000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5853425289935241427/5855000000000000000 : ℝ)*(X 0 2+X 1 2)+(98542854937/70260000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (541/128 : ℝ)) (lo := (11211/100000 : ℝ)) (hi := (3681/25000 : ℝ)) (c := (5853425289935241427/5855000000000000000 : ℝ)) (alpha := (98542854937/70260000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-202087551/1000000000 : ℝ)*X 0 0+(5411274453/10000000000 : ℝ)*X 0 1+(2622719199/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267425283/500000000 : ℝ)*X 1 0+(-2105348499/10000000000 : ℝ)*X 1 1+(5245438441/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337126423/2500000000 : ℝ)*X 2 0+(209817537/400000000 : ℝ)*X 2 1+(-1052674239/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((863922217/2000000000 : ℝ)*X 0 0+(4147457429/10000000000 : ℝ)*X 0 1+(2249172429/5000000000 : ℝ)*X 0 2+(863922217/2000000000 : ℝ)*X 1 0+(4147457429/10000000000 : ℝ)*X 1 1+(2249172429/5000000000 : ℝ)*X 1 2+(863922217/2000000000 : ℝ)*X 2 0+(4147457429/10000000000 : ℝ)*X 2 1+(2249172429/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2020887371/10000000000 : ℝ)*X 0 0+(5246033109/10000000000 : ℝ)*X 0 1+(338167293/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305660163/10000000000 : ℝ)*X 1 0+(-970055151/5000000000 : ℝ)*X 1 1+(5410676573/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305660047/10000000000 : ℝ)*X 2 0+(541067677/1000000000 : ℝ)*X 2 1+(-194011019/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2159818069/5000000000 : ℝ)*X 0 0+(4497086453/10000000000 : ℝ)*X 0 1+(829744483/2000000000 : ℝ)*X 0 2+(2159818069/5000000000 : ℝ)*X 1 0+(4497086453/10000000000 : ℝ)*X 1 1+(829744483/2000000000 : ℝ)*X 1 2+(2159818069/5000000000 : ℝ)*X 2 0+(4497086453/10000000000 : ℝ)*X 2 1+(829744483/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (131279072029048423900481431/29275000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (39812213/5000000000000 : ℝ)*(base19) + (79408041/10000000000000 : ℝ)*(base23) + (20453613/100000000000000 : ℝ)*(lower2) + (26401539/25000000000000 : ℝ)*(upper3) + (22018017/20000000000000 : ℝ)*(upper5) + (888001991909849/20000000000000 : ℝ)*(major0) + (888001991909849/20000000000000 : ℝ)*(major1) + (888001991909849/20000000000000 : ℝ)*(major2) + (1507517208272151/25000000000000 : ℝ)*(sp0) + (6030086126020427/100000000000000 : ℝ)*(sp1) + (3015043064092139/50000000000000 : ℝ)*(sp2) + (1424962357280857/50000000000000 : ℝ)*(sp3) + (18089176083/100000000000000 : ℝ)*(sp4) + (4066397029/50000000000000 : ℝ)*(sp7) + (2849932847355773/100000000000000 : ℝ)*(f.failure) + (6030086922264687/100000000000000 : ℝ)*(f.sum) + (1061579443109/439125000000000000000000000 : ℝ)*base65 + (1169824756069893569/351300000000000000000000000000000 : ℝ)*base67 + (4071699433199193569/351300000000000000000000000000000 : ℝ)*base69 + (3324646515762393569/351300000000000000000000000000000 : ℝ)*base71 + (10384672875737/1756500000000000000000000000 : ℝ)*base73 + (2538638595094893569/351300000000000000000000000000000 : ℝ)*base75 + (4932619139539593569/351300000000000000000000000000000 : ℝ)*base77 + (1444731287218406431/351300000000000000000000000000000 : ℝ)*base80 + (25487419658191/3513000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (18370431/5000000000000000000000 : ℝ)*base89 + (18370431/5000000000000000000000 : ℝ)*base91 + (18370431/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3892243206420066742467/585500000000000000000000000 : ℝ) := by norm_num
    linear_combination (574608507/50000000000000 : ℝ)*(base19) + (536985027/50000000000000 : ℝ)*(base23) + (368246723/100000000000000 : ℝ)*(lower1) + (89318523/100000000000000 : ℝ)*(upper3) + (22518669/100000000000000 : ℝ)*(lower4) + (35269879/20000000000000 : ℝ)*(upper5) + (1118031734082737/25000000000000 : ℝ)*(major0) + (1118031734082737/25000000000000 : ℝ)*(major1) + (1118031734082737/25000000000000 : ℝ)*(major2) + (116885061/6250000000000 : ℝ)*(sp2) + (303685285436091/5000000000000 : ℝ)*(sp4) + (6073704559504807/100000000000000 : ℝ)*(sp5) + (759212845573849/12500000000000 : ℝ)*(sp6) + (89704623198413/3125000000000 : ℝ)*(sp7) + (89704623198413/3125000000000 : ℝ)*(f.failure) + (303685285436091/5000000000000 : ℝ)*(f.sum) + (3272399873921/439125000000000000000000000 : ℝ)*base66 + (11380338140360587097/439125000000000000000000000000000 : ℝ)*base67 + (2562495196693912903/439125000000000000000000000000000 : ℝ)*base70 + (877582586476462097/439125000000000000000000000000000 : ℝ)*base71 + (320049208733/1756500000000000000000000000 : ℝ)*base74 + (17652688180335712097/439125000000000000000000000000000 : ℝ)*base75 + (3076237029832912903/439125000000000000000000000000000 : ℝ)*base78 + (3323967231061912903/439125000000000000000000000000000 : ℝ)*base80 + (525820743647/175650000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/50000000000000 : ℝ)*base87 + (2012511/156250000000000000000 : ℝ)*base89 + (2012511/156250000000000000000 : ℝ)*base91 + (2012511/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1369_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77896747/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3681/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11211/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2803/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14723/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1369_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1369_box_0 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1855736009/10000000000 : ℝ)*x 0 + (5388806767/10000000000 : ℝ)*x 1 + (1077761329/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1855736009/10000000000 : ℝ)^4329 ≤ (2753074434951/25000000000000 : ℝ)^3305 := by
    have hnat : (1855736009 : ℕ)^4329*25000000000000^3305 ≤ 2753074434951^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1855736009 10000000000 2753074434951 25000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5388806767/10000000000 : ℝ)^4329 ≤ (8898770356171/20000000000000 : ℝ)^3305 := by
    have hnat : (5388806767 : ℕ)^4329*20000000000000^3305 ≤ 8898770356171^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388806767 10000000000 8898770356171 20000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077761329/2000000000 : ℝ)^4329 ≤ (8898770092287/20000000000000 : ℝ)^3305 := by
    have hnat : (1077761329 : ℕ)^4329*20000000000000^3305 ≤ 8898770092287^3305*2000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077761329 2000000000 8898770092287 20000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1855736009/10000000000 : ℝ), (5388806767/10000000000 : ℝ), (1077761329/2000000000 : ℝ)] ![(2753074434951/25000000000000 : ℝ), (8898770356171/20000000000000 : ℝ), (8898770092287/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1855736009/10000000000 : ℝ)|^4329 ≤ (2753074434951/25000000000000 : ℝ)^3305
        have hw : |(-1855736009/10000000000 : ℝ)|=(1855736009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5388806767/10000000000 : ℝ)|^4329 ≤ (8898770356171/20000000000000 : ℝ)^3305
        have hw : |(5388806767/10000000000 : ℝ)|=(5388806767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077761329/2000000000 : ℝ)|^4329 ≤ (8898770092287/20000000000000 : ℝ)^3305
        have hw : |(1077761329/2000000000 : ℝ)|=(1077761329/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_box_1 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2642753451/5000000000 : ℝ)*x 0 + (-998695109/5000000000 : ℝ)*x 1 + (5388806501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642753451/5000000000 : ℝ)^4329 ≤ (43380003868879/100000000000000 : ℝ)^3305 := by
    have hnat : (2642753451 : ℕ)^4329*100000000000000^3305 ≤ 43380003868879^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642753451 5000000000 43380003868879 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (998695109/5000000000 : ℝ)^4329 ≤ (6063073609581/50000000000000 : ℝ)^3305 := by
    have hnat : (998695109 : ℕ)^4329*50000000000000^3305 ≤ 6063073609581^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998695109 5000000000 6063073609581 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5388806501/10000000000 : ℝ)^4329 ≤ (8898769780817/20000000000000 : ℝ)^3305 := by
    have hnat : (5388806501 : ℕ)^4329*20000000000000^3305 ≤ 8898769780817^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388806501 10000000000 8898769780817 20000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642753451/5000000000 : ℝ), (-998695109/5000000000 : ℝ), (5388806501/10000000000 : ℝ)] ![(43380003868879/100000000000000 : ℝ), (6063073609581/50000000000000 : ℝ), (8898769780817/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642753451/5000000000 : ℝ)|^4329 ≤ (43380003868879/100000000000000 : ℝ)^3305
        have hw : |(2642753451/5000000000 : ℝ)|=(2642753451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-998695109/5000000000 : ℝ)|^4329 ≤ (6063073609581/50000000000000 : ℝ)^3305
        have hw : |(-998695109/5000000000 : ℝ)|=(998695109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5388806501/10000000000 : ℝ)|^4329 ≤ (8898769780817/20000000000000 : ℝ)^3305
        have hw : |(5388806501/10000000000 : ℝ)|=(5388806501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_box_2 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2642753189/5000000000 : ℝ)*x 0 + (53888071/100000000 : ℝ)*x 1 + (-62418441/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642753189/5000000000 : ℝ)^4329 ≤ (21689999117871/50000000000000 : ℝ)^3305 := by
    have hnat : (2642753189 : ℕ)^4329*50000000000000^3305 ≤ 21689999117871^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642753189 5000000000 21689999117871 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (53888071/100000000 : ℝ)^4329 ≤ (1779754215289/4000000000000 : ℝ)^3305 := by
    have hnat : (53888071 : ℕ)^4329*4000000000000^3305 ≤ 1779754215289^3305*100000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53888071 100000000 1779754215289 4000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (62418441/312500000 : ℝ)^4329 ≤ (9700917101/80000000000 : ℝ)^3305 := by
    have hnat : (62418441 : ℕ)^4329*80000000000^3305 ≤ 9700917101^3305*312500000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62418441 312500000 9700917101 80000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642753189/5000000000 : ℝ), (53888071/100000000 : ℝ), (-62418441/312500000 : ℝ)] ![(21689999117871/50000000000000 : ℝ), (1779754215289/4000000000000 : ℝ), (9700917101/80000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642753189/5000000000 : ℝ)|^4329 ≤ (21689999117871/50000000000000 : ℝ)^3305
        have hw : |(2642753189/5000000000 : ℝ)|=(2642753189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(53888071/100000000 : ℝ)|^4329 ≤ (1779754215289/4000000000000 : ℝ)^3305
        have hw : |(53888071/100000000 : ℝ)|=(53888071/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-62418441/312500000 : ℝ)|^4329 ≤ (9700917101/80000000000 : ℝ)^3305
        have hw : |(-62418441/312500000 : ℝ)|=(62418441/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_box_3 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4467178989/10000000000 : ℝ)*x 0 + (424965731/1000000000 : ℝ)*x 1 + (4249657603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4467178989/10000000000 : ℝ)^4329 ≤ (8700454534117/25000000000000 : ℝ)^3305 := by
    have hnat : (4467178989 : ℕ)^4329*25000000000000^3305 ≤ 8700454534117^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4467178989 10000000000 8700454534117 25000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (424965731/1000000000 : ℝ)^4329 ≤ (32599089452827/100000000000000 : ℝ)^3305 := by
    have hnat : (424965731 : ℕ)^4329*100000000000000^3305 ≤ 32599089452827^3305*1000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424965731 1000000000 32599089452827 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4249657603/10000000000 : ℝ)^4329 ≤ (3259909239681/10000000000000 : ℝ)^3305 := by
    have hnat : (4249657603 : ℕ)^4329*10000000000000^3305 ≤ 3259909239681^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249657603 10000000000 3259909239681 10000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4467178989/10000000000 : ℝ), (424965731/1000000000 : ℝ), (4249657603/10000000000 : ℝ)] ![(8700454534117/25000000000000 : ℝ), (32599089452827/100000000000000 : ℝ), (3259909239681/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4467178989/10000000000 : ℝ)|^4329 ≤ (8700454534117/25000000000000 : ℝ)^3305
        have hw : |(4467178989/10000000000 : ℝ)|=(4467178989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(424965731/1000000000 : ℝ)|^4329 ≤ (32599089452827/100000000000000 : ℝ)^3305
        have hw : |(424965731/1000000000 : ℝ)|=(424965731/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4249657603/10000000000 : ℝ)|^4329 ≤ (3259909239681/10000000000000 : ℝ)^3305
        have hw : |(4249657603/10000000000 : ℝ)|=(4249657603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_box_4 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-547190251/2500000000 : ℝ)*x 0 + (329093359/625000000 : ℝ)*x 1 + (329093347/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (547190251/2500000000 : ℝ)^4329 ≤ (6835017543407/50000000000000 : ℝ)^3305 := by
    have hnat : (547190251 : ℕ)^4329*50000000000000^3305 ≤ 6835017543407^3305*2500000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547190251 2500000000 6835017543407 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329093359/625000000 : ℝ)^4329 ≤ (2158249174013/5000000000000 : ℝ)^3305 := by
    have hnat : (329093359 : ℕ)^4329*5000000000000^3305 ≤ 2158249174013^3305*625000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329093359 625000000 2158249174013 5000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329093347/625000000 : ℝ)^4329 ≤ (8632996283727/20000000000000 : ℝ)^3305 := by
    have hnat : (329093347 : ℕ)^4329*20000000000000^3305 ≤ 8632996283727^3305*625000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329093347 625000000 8632996283727 20000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-547190251/2500000000 : ℝ), (329093359/625000000 : ℝ), (329093347/625000000 : ℝ)] ![(6835017543407/50000000000000 : ℝ), (2158249174013/5000000000000 : ℝ), (8632996283727/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-547190251/2500000000 : ℝ)|^4329 ≤ (6835017543407/50000000000000 : ℝ)^3305
        have hw : |(-547190251/2500000000 : ℝ)|=(547190251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329093359/625000000 : ℝ)|^4329 ≤ (2158249174013/5000000000000 : ℝ)^3305
        have hw : |(329093359/625000000 : ℝ)|=(329093359/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329093347/625000000 : ℝ)|^4329 ≤ (8632996283727/20000000000000 : ℝ)^3305
        have hw : |(329093347/625000000 : ℝ)|=(329093347/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_box_5 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2686010349/5000000000 : ℝ)*x 0 + (-127941099/625000000 : ℝ)*x 1 + (5265493977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686010349/5000000000 : ℝ)^4329 ≤ (22156199684969/50000000000000 : ℝ)^3305 := by
    have hnat : (2686010349 : ℕ)^4329*50000000000000^3305 ≤ 22156199684969^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686010349 5000000000 22156199684969 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (127941099/625000000 : ℝ)^4329 ≤ (3130653658879/25000000000000 : ℝ)^3305 := by
    have hnat : (127941099 : ℕ)^4329*25000000000000^3305 ≤ 3130653658879^3305*625000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127941099 625000000 3130653658879 25000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265493977/10000000000 : ℝ)^4329 ≤ (43164985982129/100000000000000 : ℝ)^3305 := by
    have hnat : (5265493977 : ℕ)^4329*100000000000000^3305 ≤ 43164985982129^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265493977 10000000000 43164985982129 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686010349/5000000000 : ℝ), (-127941099/625000000 : ℝ), (5265493977/10000000000 : ℝ)] ![(22156199684969/50000000000000 : ℝ), (3130653658879/25000000000000 : ℝ), (43164985982129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686010349/5000000000 : ℝ)|^4329 ≤ (22156199684969/50000000000000 : ℝ)^3305
        have hw : |(2686010349/5000000000 : ℝ)|=(2686010349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-127941099/625000000 : ℝ)|^4329 ≤ (3130653658879/25000000000000 : ℝ)^3305
        have hw : |(-127941099/625000000 : ℝ)|=(127941099/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265493977/10000000000 : ℝ)|^4329 ≤ (43164985982129/100000000000000 : ℝ)^3305
        have hw : |(5265493977/10000000000 : ℝ)|=(5265493977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_box_6 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (671502659/1250000000 : ℝ)*x 0 + (526549351/1000000000 : ℝ)*x 1 + (-409411487/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671502659/1250000000 : ℝ)^4329 ≤ (11078101392927/25000000000000 : ℝ)^3305 := by
    have hnat : (671502659 : ℕ)^4329*25000000000000^3305 ≤ 11078101392927^3305*1250000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671502659 1250000000 11078101392927 25000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526549351/1000000000 : ℝ)^4329 ≤ (21582490483827/50000000000000 : ℝ)^3305 := by
    have hnat : (526549351 : ℕ)^4329*50000000000000^3305 ≤ 21582490483827^3305*1000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526549351 1000000000 21582490483827 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (409411487/2000000000 : ℝ)^4329 ≤ (6261306720809/50000000000000 : ℝ)^3305 := by
    have hnat : (409411487 : ℕ)^4329*50000000000000^3305 ≤ 6261306720809^3305*2000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409411487 2000000000 6261306720809 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671502659/1250000000 : ℝ), (526549351/1000000000 : ℝ), (-409411487/2000000000 : ℝ)] ![(11078101392927/25000000000000 : ℝ), (21582490483827/50000000000000 : ℝ), (6261306720809/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671502659/1250000000 : ℝ)|^4329 ≤ (11078101392927/25000000000000 : ℝ)^3305
        have hw : |(671502659/1250000000 : ℝ)|=(671502659/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526549351/1000000000 : ℝ)|^4329 ≤ (21582490483827/50000000000000 : ℝ)^3305
        have hw : |(526549351/1000000000 : ℝ)|=(526549351/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-409411487/2000000000 : ℝ)|^4329 ≤ (6261306720809/50000000000000 : ℝ)^3305
        have hw : |(-409411487/2000000000 : ℝ)|=(409411487/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_box_7 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (208553889/500000000 : ℝ)*x 0 + (2198827649/5000000000 : ℝ)*x 1 + (2198827701/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208553889/500000000 : ℝ)^4329 ≤ (397647692853/1250000000000 : ℝ)^3305 := by
    have hnat : (208553889 : ℕ)^4329*1250000000000^3305 ≤ 397647692853^3305*500000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208553889 500000000 397647692853 1250000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2198827649/5000000000 : ℝ)^4329 ≤ (17047045874251/50000000000000 : ℝ)^3305 := by
    have hnat : (2198827649 : ℕ)^4329*50000000000000^3305 ≤ 17047045874251^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198827649 5000000000 17047045874251 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2198827701/5000000000 : ℝ)^4329 ≤ (34094092804607/100000000000000 : ℝ)^3305 := by
    have hnat : (2198827701 : ℕ)^4329*100000000000000^3305 ≤ 34094092804607^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198827701 5000000000 34094092804607 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(208553889/500000000 : ℝ), (2198827649/5000000000 : ℝ), (2198827701/5000000000 : ℝ)] ![(397647692853/1250000000000 : ℝ), (17047045874251/50000000000000 : ℝ), (34094092804607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(208553889/500000000 : ℝ)|^4329 ≤ (397647692853/1250000000000 : ℝ)^3305
        have hw : |(208553889/500000000 : ℝ)|=(208553889/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2198827649/5000000000 : ℝ)|^4329 ≤ (17047045874251/50000000000000 : ℝ)^3305
        have hw : |(2198827649/5000000000 : ℝ)|=(2198827649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2198827701/5000000000 : ℝ)|^4329 ≤ (34094092804607/100000000000000 : ℝ)^3305
        have hw : |(2198827701/5000000000 : ℝ)|=(2198827701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_box_8 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-529689317/2500000000 : ℝ)*x 0 + (5180475639/10000000000 : ℝ)*x 1 + (2701406987/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529689317/2500000000 : ℝ)^4329 ≤ (13100218182563/100000000000000 : ℝ)^3305 := by
    have hnat : (529689317 : ℕ)^4329*100000000000000^3305 ≤ 13100218182563^3305*2500000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529689317 2500000000 13100218182563 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180475639/10000000000 : ℝ)^4329 ≤ (8450876433063/20000000000000 : ℝ)^3305 := by
    have hnat : (5180475639 : ℕ)^4329*20000000000000^3305 ≤ 8450876433063^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180475639 10000000000 8450876433063 20000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701406987/5000000000 : ℝ)^4329 ≤ (44645399638957/100000000000000 : ℝ)^3305 := by
    have hnat : (2701406987 : ℕ)^4329*100000000000000^3305 ≤ 44645399638957^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701406987 5000000000 44645399638957 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-529689317/2500000000 : ℝ), (5180475639/10000000000 : ℝ), (2701406987/5000000000 : ℝ)] ![(13100218182563/100000000000000 : ℝ), (8450876433063/20000000000000 : ℝ), (44645399638957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-529689317/2500000000 : ℝ)|^4329 ≤ (13100218182563/100000000000000 : ℝ)^3305
        have hw : |(-529689317/2500000000 : ℝ)|=(529689317/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180475639/10000000000 : ℝ)|^4329 ≤ (8450876433063/20000000000000 : ℝ)^3305
        have hw : |(5180475639/10000000000 : ℝ)|=(5180475639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701406987/5000000000 : ℝ)|^4329 ≤ (44645399638957/100000000000000 : ℝ)^3305
        have hw : |(2701406987/5000000000 : ℝ)|=(2701406987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_box_9 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2637837103/5000000000 : ℝ)*x 0 + (-995809073/5000000000 : ℝ)*x 1 + (5402814137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637837103/5000000000 : ℝ)^4329 ≤ (5409291285409/12500000000000 : ℝ)^3305 := by
    have hnat : (2637837103 : ℕ)^4329*12500000000000^3305 ≤ 5409291285409^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637837103 5000000000 5409291285409 12500000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (995809073/5000000000 : ℝ)^4329 ≤ (1510033537449/12500000000000 : ℝ)^3305 := by
    have hnat : (995809073 : ℕ)^4329*12500000000000^3305 ≤ 1510033537449^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995809073 5000000000 1510033537449 12500000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5402814137/10000000000 : ℝ)^4329 ≤ (5580675175401/12500000000000 : ℝ)^3305 := by
    have hnat : (5402814137 : ℕ)^4329*12500000000000^3305 ≤ 5580675175401^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402814137 10000000000 5580675175401 12500000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637837103/5000000000 : ℝ), (-995809073/5000000000 : ℝ), (5402814137/10000000000 : ℝ)] ![(5409291285409/12500000000000 : ℝ), (1510033537449/12500000000000 : ℝ), (5580675175401/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637837103/5000000000 : ℝ)|^4329 ≤ (5409291285409/12500000000000 : ℝ)^3305
        have hw : |(2637837103/5000000000 : ℝ)|=(2637837103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-995809073/5000000000 : ℝ)|^4329 ≤ (1510033537449/12500000000000 : ℝ)^3305
        have hw : |(-995809073/5000000000 : ℝ)|=(995809073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5402814137/10000000000 : ℝ)|^4329 ≤ (5580675175401/12500000000000 : ℝ)^3305
        have hw : |(5402814137/10000000000 : ℝ)|=(5402814137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_box_10 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275674413/10000000000 : ℝ)*x 0 + (5402814183/10000000000 : ℝ)*x 1 + (-497904451/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275674413/10000000000 : ℝ)^4329 ≤ (43274332507293/100000000000000 : ℝ)^3305 := by
    have hnat : (5275674413 : ℕ)^4329*100000000000000^3305 ≤ 43274332507293^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275674413 10000000000 43274332507293 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5402814183/10000000000 : ℝ)^4329 ≤ (8929080380219/20000000000000 : ℝ)^3305 := by
    have hnat : (5402814183 : ℕ)^4329*20000000000000^3305 ≤ 8929080380219^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402814183 10000000000 8929080380219 20000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (497904451/2500000000 : ℝ)^4329 ≤ (12080265582447/100000000000000 : ℝ)^3305 := by
    have hnat : (497904451 : ℕ)^4329*100000000000000^3305 ≤ 12080265582447^3305*2500000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497904451 2500000000 12080265582447 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275674413/10000000000 : ℝ), (5402814183/10000000000 : ℝ), (-497904451/2500000000 : ℝ)] ![(43274332507293/100000000000000 : ℝ), (8929080380219/20000000000000 : ℝ), (12080265582447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275674413/10000000000 : ℝ)|^4329 ≤ (43274332507293/100000000000000 : ℝ)^3305
        have hw : |(5275674413/10000000000 : ℝ)|=(5275674413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5402814183/10000000000 : ℝ)|^4329 ≤ (8929080380219/20000000000000 : ℝ)^3305
        have hw : |(5402814183/10000000000 : ℝ)|=(5402814183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-497904451/2500000000 : ℝ)|^4329 ≤ (12080265582447/100000000000000 : ℝ)^3305
        have hw : |(-497904451/2500000000 : ℝ)|=(497904451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_box_11 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4500255083/10000000000 : ℝ)*x 0 + (211641617/500000000 : ℝ)*x 1 + (4232831807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4500255083/10000000000 : ℝ)^4329 ≤ (35139724166829/100000000000000 : ℝ)^3305 := by
    have hnat : (4500255083 : ℕ)^4329*100000000000000^3305 ≤ 35139724166829^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500255083 10000000000 35139724166829 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211641617/500000000 : ℝ)^4329 ≤ (32430140584769/100000000000000 : ℝ)^3305 := by
    have hnat : (211641617 : ℕ)^4329*100000000000000^3305 ≤ 32430140584769^3305*500000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211641617 500000000 32430140584769 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4232831807/10000000000 : ℝ)^4329 ≤ (3243013523591/10000000000000 : ℝ)^3305 := by
    have hnat : (4232831807 : ℕ)^4329*10000000000000^3305 ≤ 3243013523591^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232831807 10000000000 3243013523591 10000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4500255083/10000000000 : ℝ), (211641617/500000000 : ℝ), (4232831807/10000000000 : ℝ)] ![(35139724166829/100000000000000 : ℝ), (32430140584769/100000000000000 : ℝ), (3243013523591/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4500255083/10000000000 : ℝ)|^4329 ≤ (35139724166829/100000000000000 : ℝ)^3305
        have hw : |(4500255083/10000000000 : ℝ)|=(4500255083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(211641617/500000000 : ℝ)|^4329 ≤ (32430140584769/100000000000000 : ℝ)^3305
        have hw : |(211641617/500000000 : ℝ)|=(211641617/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4232831807/10000000000 : ℝ)|^4329 ≤ (3243013523591/10000000000000 : ℝ)^3305
        have hw : |(4232831807/10000000000 : ℝ)|=(4232831807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_box_12 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1926025891/10000000000 : ℝ)*x 0 + (5471678841/10000000000 : ℝ)*x 1 + (328400219/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1926025891/10000000000 : ℝ)^4329 ≤ (11561825783199/100000000000000 : ℝ)^3305 := by
    have hnat : (1926025891 : ℕ)^4329*100000000000000^3305 ≤ 11561825783199^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1926025891 10000000000 11561825783199 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5471678841/10000000000 : ℝ)^4329 ≤ (45392234781749/100000000000000 : ℝ)^3305 := by
    have hnat : (5471678841 : ℕ)^4329*100000000000000^3305 ≤ 45392234781749^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471678841 10000000000 45392234781749 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (328400219/625000000 : ℝ)^4329 ≤ (43045939415379/100000000000000 : ℝ)^3305 := by
    have hnat : (328400219 : ℕ)^4329*100000000000000^3305 ≤ 43045939415379^3305*625000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328400219 625000000 43045939415379 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1926025891/10000000000 : ℝ), (5471678841/10000000000 : ℝ), (328400219/625000000 : ℝ)] ![(11561825783199/100000000000000 : ℝ), (45392234781749/100000000000000 : ℝ), (43045939415379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1926025891/10000000000 : ℝ)|^4329 ≤ (11561825783199/100000000000000 : ℝ)^3305
        have hw : |(-1926025891/10000000000 : ℝ)|=(1926025891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5471678841/10000000000 : ℝ)|^4329 ≤ (45392234781749/100000000000000 : ℝ)^3305
        have hw : |(5471678841/10000000000 : ℝ)|=(5471678841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(328400219/625000000 : ℝ)|^4329 ≤ (43045939415379/100000000000000 : ℝ)^3305
        have hw : |(328400219/625000000 : ℝ)|=(328400219/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_box_13 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5379798893/10000000000 : ℝ)*x 0 + (-410284431/2000000000 : ℝ)*x 1 + (5254403939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5379798893/10000000000 : ℝ)^4329 ≤ (5549557191961/12500000000000 : ℝ)^3305 := by
    have hnat : (5379798893 : ℕ)^4329*12500000000000^3305 ≤ 5549557191961^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5379798893 10000000000 5549557191961 12500000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (410284431/2000000000 : ℝ)^4329 ≤ (12557598356059/100000000000000 : ℝ)^3305 := by
    have hnat : (410284431 : ℕ)^4329*100000000000000^3305 ≤ 12557598356059^3305*2000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410284431 2000000000 12557598356059 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254403939/10000000000 : ℝ)^4329 ≤ (6725928763/15625000000 : ℝ)^3305 := by
    have hnat : (5254403939 : ℕ)^4329*15625000000^3305 ≤ 6725928763^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254403939 10000000000 6725928763 15625000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5379798893/10000000000 : ℝ), (-410284431/2000000000 : ℝ), (5254403939/10000000000 : ℝ)] ![(5549557191961/12500000000000 : ℝ), (12557598356059/100000000000000 : ℝ), (6725928763/15625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5379798893/10000000000 : ℝ)|^4329 ≤ (5549557191961/12500000000000 : ℝ)^3305
        have hw : |(5379798893/10000000000 : ℝ)|=(5379798893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-410284431/2000000000 : ℝ)|^4329 ≤ (12557598356059/100000000000000 : ℝ)^3305
        have hw : |(-410284431/2000000000 : ℝ)|=(410284431/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254403939/10000000000 : ℝ)|^4329 ≤ (6725928763/15625000000 : ℝ)^3305
        have hw : |(5254403939/10000000000 : ℝ)|=(5254403939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_box_14 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5379799793/10000000000 : ℝ)*x 0 + (5254403023/10000000000 : ℝ)*x 1 + (-2051422169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5379799793/10000000000 : ℝ)^4329 ≤ (44396467264077/100000000000000 : ℝ)^3305 := by
    have hnat : (5379799793 : ℕ)^4329*100000000000000^3305 ≤ 44396467264077^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5379799793 10000000000 44396467264077 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5254403023/10000000000 : ℝ)^4329 ≤ (860918685079/2000000000000 : ℝ)^3305 := by
    have hnat : (5254403023 : ℕ)^4329*2000000000000^3305 ≤ 860918685079^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254403023 10000000000 860918685079 2000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2051422169/10000000000 : ℝ)^4329 ≤ (12557598468311/100000000000000 : ℝ)^3305 := by
    have hnat : (2051422169 : ℕ)^4329*100000000000000^3305 ≤ 12557598468311^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2051422169 10000000000 12557598468311 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5379799793/10000000000 : ℝ), (5254403023/10000000000 : ℝ), (-2051422169/10000000000 : ℝ)] ![(44396467264077/100000000000000 : ℝ), (860918685079/2000000000000 : ℝ), (12557598468311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5379799793/10000000000 : ℝ)|^4329 ≤ (44396467264077/100000000000000 : ℝ)^3305
        have hw : |(5379799793/10000000000 : ℝ)|=(5379799793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5254403023/10000000000 : ℝ)|^4329 ≤ (860918685079/2000000000000 : ℝ)^3305
        have hw : |(5254403023/10000000000 : ℝ)|=(5254403023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2051422169/10000000000 : ℝ)|^4329 ≤ (12557598468311/100000000000000 : ℝ)^3305
        have hw : |(-2051422169/10000000000 : ℝ)|=(2051422169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_box_15 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (207200007/500000000 : ℝ)*x 0 + (2205477249/5000000000 : ℝ)*x 1 + (882190879/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (207200007/500000000 : ℝ)^4329 ≤ (15770793989893/50000000000000 : ℝ)^3305 := by
    have hnat : (207200007 : ℕ)^4329*50000000000000^3305 ≤ 15770793989893^3305*500000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207200007 500000000 15770793989893 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2205477249/5000000000 : ℝ)^4329 ≤ (17114603263649/50000000000000 : ℝ)^3305 := by
    have hnat : (2205477249 : ℕ)^4329*50000000000000^3305 ≤ 17114603263649^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205477249 5000000000 17114603263649 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (882190879/2000000000 : ℝ)^4329 ≤ (2139325342523/6250000000000 : ℝ)^3305 := by
    have hnat : (882190879 : ℕ)^4329*6250000000000^3305 ≤ 2139325342523^3305*2000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      882190879 2000000000 2139325342523 6250000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(207200007/500000000 : ℝ), (2205477249/5000000000 : ℝ), (882190879/2000000000 : ℝ)] ![(15770793989893/50000000000000 : ℝ), (17114603263649/50000000000000 : ℝ), (2139325342523/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(207200007/500000000 : ℝ)|^4329 ≤ (15770793989893/50000000000000 : ℝ)^3305
        have hw : |(207200007/500000000 : ℝ)|=(207200007/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2205477249/5000000000 : ℝ)|^4329 ≤ (17114603263649/50000000000000 : ℝ)^3305
        have hw : |(2205477249/5000000000 : ℝ)|=(2205477249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(882190879/2000000000 : ℝ)|^4329 ≤ (2139325342523/6250000000000 : ℝ)^3305
        have hw : |(882190879/2000000000 : ℝ)|=(882190879/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1369_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77896747/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14723/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2803/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62867/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29497/50000 : ℝ) ∧ (80111/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84457/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14723/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2803/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14723/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2803/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14723/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2803/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14723/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2803/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14723/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2803/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14723/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2803/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2803/25000 : ℝ) ^ (541/128 : ℝ) ≤ (601597743435381/6250000000000000000 : ℝ) := by
    have hpowers : (2803/25000 : ℝ)^541 ≤ (601597743435381/6250000000000000000 : ℝ)^128 := by
      have hnat : (2803 : ℕ)^541*6250000000000000000^128 ≤ 601597743435381^128*25000^541 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2803 25000 601597743435381 6250000000000000000 541 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2803/25000 : ℝ)) (X := (601597743435381/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14723/100000 : ℝ) ^ (541/128 : ℝ) ≤ (3805348407912933/12500000000000000000 : ℝ) := by
    have hpowers : (14723/100000 : ℝ)^541 ≤ (3805348407912933/12500000000000000000 : ℝ)^128 := by
      have hnat : (14723 : ℕ)^541*12500000000000000000^128 ≤ 3805348407912933^128*100000^541 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14723 100000 3805348407912933 12500000000000000000 541 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14723/100000 : ℝ)) (X := (3805348407912933/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125601597743435381/3125000000000000000 : ℝ) ≤ (10000455446082843/10000000000000000 : ℝ) ^ (541/128 : ℝ) := by
    have hpowers : (3125601597743435381/3125000000000000000 : ℝ)^128 ≤ (10000455446082843/10000000000000000 : ℝ)^541 := by
      have hnat : (3125601597743435381 : ℕ)^128*10000000000000000^541 ≤ 10000455446082843^541*3125000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125601597743435381 3125000000000000000 10000455446082843 10000000000000000 128 541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000455446082843/10000000000000000 : ℝ)) (X := (3125601597743435381/3125000000000000000 : ℝ)) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (2501001708778956739/2500000000000000000 : ℝ) ≤ (2000189573557721/2000000000000000 : ℝ) ^ (541/128 : ℝ) := by
    have hpowers : (2501001708778956739/2500000000000000000 : ℝ)^128 ≤ (2000189573557721/2000000000000000 : ℝ)^541 := by
      have hnat : (2501001708778956739 : ℕ)^128*2000000000000000^541 ≤ 2000189573557721^541*2500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501001708778956739 2500000000000000000 2000189573557721 2000000000000000 128 541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000189573557721/2000000000000000 : ℝ)) (X := (2501001708778956739/2500000000000000000 : ℝ)) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253805348407912933/6250000000000000000 : ℝ) ≤ (10001440289494367/10000000000000000 : ℝ) ^ (541/128 : ℝ) := by
    have hpowers : (6253805348407912933/6250000000000000000 : ℝ)^128 ≤ (10001440289494367/10000000000000000 : ℝ)^541 := by
      have hnat : (6253805348407912933 : ℕ)^128*10000000000000000^541 ≤ 10001440289494367^541*6250000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253805348407912933 6250000000000000000 10001440289494367 10000000000000000 128 541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001440289494367/10000000000000000 : ℝ)) (X := (6253805348407912933/6250000000000000000 : ℝ)) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(601597743435381/6250000000000000000 : ℝ) ≤ ((7020111401373370937/7022000000000000000 : ℝ)+2*(246210852881/175550000000000 : ℝ)*(2803/25000 : ℝ))^(541/128 : ℝ) := by
    rw [show (7020111401373370937/7022000000000000000 : ℝ)+2*(246210852881/175550000000000 : ℝ)*(2803/25000 : ℝ)=(10000455446082843/10000000000000000 : ℝ) by norm_num, show 1+2*(601597743435381/6250000000000000000 : ℝ)=(3125601597743435381/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3805348407912933/12500000000000000000 : ℝ)+(601597743435381/6250000000000000000 : ℝ) ≤ ((7020111401373370937/7022000000000000000 : ℝ)+(246210852881/175550000000000 : ℝ)*((14723/100000 : ℝ)+(2803/25000 : ℝ)))^(541/128 : ℝ) := by
    rw [show (7020111401373370937/7022000000000000000 : ℝ)+(246210852881/175550000000000 : ℝ)*((14723/100000 : ℝ)+(2803/25000 : ℝ))=(2000189573557721/2000000000000000 : ℝ) by norm_num, show 1+(3805348407912933/12500000000000000000 : ℝ)+(601597743435381/6250000000000000000 : ℝ)=(2501001708778956739/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3805348407912933/12500000000000000000 : ℝ) ≤ ((7020111401373370937/7022000000000000000 : ℝ)+2*(246210852881/175550000000000 : ℝ)*(14723/100000 : ℝ))^(541/128 : ℝ) := by
    rw [show (7020111401373370937/7022000000000000000 : ℝ)+2*(246210852881/175550000000000 : ℝ)*(14723/100000 : ℝ)=(10001440289494367/10000000000000000 : ℝ) by norm_num, show 1+2*(3805348407912933/12500000000000000000 : ℝ)=(6253805348407912933/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7020111401373370937/7022000000000000000 : ℝ)*(X 1 0+X 2 0)+(246210852881/175550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (541/128 : ℝ)) (lo := (2803/25000 : ℝ)) (hi := (14723/100000 : ℝ)) (c := (7020111401373370937/7022000000000000000 : ℝ)) (alpha := (246210852881/175550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7020111401373370937/7022000000000000000 : ℝ)*(X 0 1+X 2 1)+(246210852881/175550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (541/128 : ℝ)) (lo := (2803/25000 : ℝ)) (hi := (14723/100000 : ℝ)) (c := (7020111401373370937/7022000000000000000 : ℝ)) (alpha := (246210852881/175550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7020111401373370937/7022000000000000000 : ℝ)*(X 0 2+X 1 2)+(246210852881/175550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (541/128 : ℝ)) (lo := (2803/25000 : ℝ)) (hi := (14723/100000 : ℝ)) (c := (7020111401373370937/7022000000000000000 : ℝ)) (alpha := (246210852881/175550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1855736009/10000000000 : ℝ)*X 0 0+(5388806767/10000000000 : ℝ)*X 0 1+(1077761329/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2642753451/5000000000 : ℝ)*X 1 0+(-998695109/5000000000 : ℝ)*X 1 1+(5388806501/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2642753189/5000000000 : ℝ)*X 2 0+(53888071/100000000 : ℝ)*X 2 1+(-62418441/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4467178989/10000000000 : ℝ)*X 0 0+(424965731/1000000000 : ℝ)*X 0 1+(4249657603/10000000000 : ℝ)*X 0 2+(4467178989/10000000000 : ℝ)*X 1 0+(424965731/1000000000 : ℝ)*X 1 1+(4249657603/10000000000 : ℝ)*X 1 2+(4467178989/10000000000 : ℝ)*X 2 0+(424965731/1000000000 : ℝ)*X 2 1+(4249657603/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-547190251/2500000000 : ℝ)*X 0 0+(329093359/625000000 : ℝ)*X 0 1+(329093347/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2686010349/5000000000 : ℝ)*X 1 0+(-127941099/625000000 : ℝ)*X 1 1+(5265493977/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((671502659/1250000000 : ℝ)*X 2 0+(526549351/1000000000 : ℝ)*X 2 1+(-409411487/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((208553889/500000000 : ℝ)*X 0 0+(2198827649/5000000000 : ℝ)*X 0 1+(2198827701/5000000000 : ℝ)*X 0 2+(208553889/500000000 : ℝ)*X 1 0+(2198827649/5000000000 : ℝ)*X 1 1+(2198827701/5000000000 : ℝ)*X 1 2+(208553889/500000000 : ℝ)*X 2 0+(2198827649/5000000000 : ℝ)*X 2 1+(2198827701/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-529689317/2500000000 : ℝ)*X 0 0+(5180475639/10000000000 : ℝ)*X 0 1+(2701406987/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2637837103/5000000000 : ℝ)*X 1 0+(-995809073/5000000000 : ℝ)*X 1 1+(5402814137/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5275674413/10000000000 : ℝ)*X 2 0+(5402814183/10000000000 : ℝ)*X 2 1+(-497904451/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4500255083/10000000000 : ℝ)*X 0 0+(211641617/500000000 : ℝ)*X 0 1+(4232831807/10000000000 : ℝ)*X 0 2+(4500255083/10000000000 : ℝ)*X 1 0+(211641617/500000000 : ℝ)*X 1 1+(4232831807/10000000000 : ℝ)*X 1 2+(4500255083/10000000000 : ℝ)*X 2 0+(211641617/500000000 : ℝ)*X 2 1+(4232831807/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1926025891/10000000000 : ℝ)*X 0 0+(5471678841/10000000000 : ℝ)*X 0 1+(328400219/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5379798893/10000000000 : ℝ)*X 1 0+(-410284431/2000000000 : ℝ)*X 1 1+(5254403939/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5379799793/10000000000 : ℝ)*X 2 0+(5254403023/10000000000 : ℝ)*X 2 1+(-2051422169/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((207200007/500000000 : ℝ)*X 0 0+(2205477249/5000000000 : ℝ)*X 0 1+(882190879/2000000000 : ℝ)*X 0 2+(207200007/500000000 : ℝ)*X 1 0+(2205477249/5000000000 : ℝ)*X 1 1+(882190879/2000000000 : ℝ)*X 1 2+(207200007/500000000 : ℝ)*X 2 0+(2205477249/5000000000 : ℝ)*X 2 1+(882190879/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62867/100000 : ℝ) ≤ (-220716848232377407014703213532157/351100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21897109/100000000000000 : ℝ)*(lower2) + (44918953/50000000000000 : ℝ)*(upper4) + (462929/312500000000 : ℝ)*(upper5) + (2950803742767229/100000000000000 : ℝ)*(major0) + (2950803742767229/100000000000000 : ℝ)*(major1) + (2950803742767229/100000000000000 : ℝ)*(major2) + (12113771699/100000000000000 : ℝ)*(sp2) + (1310249353/20000000000000 : ℝ)*(sp3) + (503562902364911/12500000000000 : ℝ)*(sp4) + (2014247631176567/50000000000000 : ℝ)*(sp5) + (4028502046963253/100000000000000 : ℝ)*(sp6) + (947020783920217/50000000000000 : ℝ)*(sp7) + (683863479/6250000000000 : ℝ)*(sp8) + (18898381817/100000000000000 : ℝ)*(sp13) + (2367560148859/125000000000 : ℝ)*(f.failure) + (503564270091869/12500000000000 : ℝ)*(f.sum) + (208903779325943/17555000000000000000000000000 : ℝ)*base65 + (2235247719624583573/702200000000000000000000000000000 : ℝ)*base67 + (4910430698589583573/702200000000000000000000000000000 : ℝ)*base69 + (8881494764054983573/702200000000000000000000000000000 : ℝ)*base71 + (114457768636507/17555000000000000000000000000 : ℝ)*base74 + (7627150251277783573/702200000000000000000000000000000 : ℝ)*base75 + (1720727457119983573/702200000000000000000000000000000 : ℝ)*base77 + (5012654210028183573/702200000000000000000000000000000 : ℝ)*base79 + (18072806920199/8777500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (49173/6250000000000000000 : ℝ)*base89 + (49173/6250000000000000000 : ℝ)*base91 + (49173/6250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (29497/50000 : ℝ) ≤ (8285458809021363517202131598691/14044000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19796739/100000000000000 : ℝ)*(lower1) + (19024589/25000000000000 : ℝ)*(upper2) + (545337/100000000000000 : ℝ)*(upper5) + (120815417613027/4000000000000 : ℝ)*(major0) + (120815417613027/4000000000000 : ℝ)*(major1) + (120815417613027/4000000000000 : ℝ)*(major2) + (1020598425141439/25000000000000 : ℝ)*(sp0) + (510293271440959/12500000000000 : ℝ)*(sp1) + (2041192036612219/50000000000000 : ℝ)*(sp2) + (969354958943893/50000000000000 : ℝ)*(sp3) + (10436330587/100000000000000 : ℝ)*(sp6) + (976115063/100000000000000 : ℝ)*(sp7) + (48338027353/100000000000000 : ℝ)*(sp9) + (202247317/25000000000000 : ℝ)*(sp12) + (1938710894002849/100000000000000 : ℝ)*(f.failure) + (255149656847189/6250000000000 : ℝ)*(f.sum) + (3079942734737/877750000000000000000000000 : ℝ)*base65 + (93286522489435701/28088000000000000000000000000000 : ℝ)*base68 + (94064062988011701/28088000000000000000000000000000 : ℝ)*base70 + (143972966749451701/28088000000000000000000000000000 : ℝ)*base72 + (1385482709553/351100000000000000000000000 : ℝ)*base74 + (3796009774019701/28088000000000000000000000000000 : ℝ)*base76 + (134933219373659701/28088000000000000000000000000000 : ℝ)*base78 + (22447208211275701/28088000000000000000000000000000 : ℝ)*base80 + (24586667822657/3511000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (4167797/5000000000000000000000 : ℝ)*base90 + (4167797/5000000000000000000000 : ℝ)*base92 + (4167797/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (80111/100000 : ℝ) ≤ (281278295822537211719177679924801/351100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11978913/100000000000000 : ℝ)*(upper0) + (31393263/100000000000000 : ℝ)*(upper1) + (38808193/20000000000000 : ℝ)*(upper4) + (3331332875670909/100000000000000 : ℝ)*(major0) + (3331332875670909/100000000000000 : ℝ)*(major1) + (3331332875670909/100000000000000 : ℝ)*(major2) + (5960218959/5000000000000 : ℝ)*(sp1) + (22187774919/10000000000000 : ℝ)*(sp2) + (73903978451/100000000000000 : ℝ)*(sp3) + (906959349/20000000000000 : ℝ)*(sp4) + (89953127097083/2000000000000 : ℝ)*(sp8) + (1124385421317929/25000000000000 : ℝ)*(sp9) + (562179876487713/12500000000000 : ℝ)*(sp10) + (2138226476954599/100000000000000 : ℝ)*(sp11) + (42766007618661/2000000000000 : ℝ)*(f.failure) + (899532177930179/20000000000000 : ℝ)*(f.sum) + (25899358412989/8777500000000000000000000000 : ℝ)*base65 + (2326514480430131733/702200000000000000000000000000000 : ℝ)*base67 + (2974469470040931733/702200000000000000000000000000000 : ℝ)*base69 + (4697681307396268267/702200000000000000000000000000000 : ℝ)*base72 + (41801665538061/2194375000000000000000000000 : ℝ)*base73 + (4022334141809468267/702200000000000000000000000000000 : ℝ)*base76 + (5431149424828531733/702200000000000000000000000000000 : ℝ)*base77 + (20104672445285731733/702200000000000000000000000000000 : ℝ)*base79 + (15422481270023/4388750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (604233/100000000000000000000 : ℝ)*base90 + (604233/100000000000000000000 : ℝ)*base92 + (604233/100000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-84457/100000 : ℝ) ≤ (-148259355266686439453012191123251/175550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (624931/2500000000000 : ℝ)*(upper1) + (143199727/100000000000000 : ℝ)*(lower2) + (223537441/100000000000000 : ℝ)*(upper3) + (37190257/10000000000000 : ℝ)*(upper5) + (3368097035111959/100000000000000 : ℝ)*(major0) + (3368097035111959/100000000000000 : ℝ)*(major1) + (3368097035111959/100000000000000 : ℝ)*(major2) + (93904397/6250000000000 : ℝ)*(sp4) + (4355270593/1250000000000 : ℝ)*(sp6) + (50429825629/50000000000000 : ℝ)*(sp7) + (2301222790647981/50000000000000 : ℝ)*(sp12) + (920489416753263/20000000000000 : ℝ)*(sp13) + (2301049331059437/50000000000000 : ℝ)*(sp14) + (270224691020893/12500000000000 : ℝ)*(sp15) + (1080949193909201/50000000000000 : ℝ)*(f.failure) + (920489416753263/20000000000000 : ℝ)*(f.sum) + (2083647117781/548593750000000000000000000 : ℝ)*base66 + (3372224900629695583/702200000000000000000000000000000 : ℝ)*base67 + (4456475254858704417/702200000000000000000000000000000 : ℝ)*base70 + (2853157406042104417/702200000000000000000000000000000 : ℝ)*base72 + (107780881077853/17555000000000000000000000000 : ℝ)*base73 + (10334235883951304417/702200000000000000000000000000000 : ℝ)*base76 + (1830225777369504417/702200000000000000000000000000000 : ℝ)*base78 + (1068103495428704417/702200000000000000000000000000000 : ℝ)*base80 + (3640420179899/2194375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (3730853/2500000000000000000000 : ℝ)*base90 + (3730853/2500000000000000000000 : ℝ)*base92 + (3730853/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1369_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77896747/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14723/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2803/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62867/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29497/50000 : ℝ) else (80111/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84457/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1369_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1369_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77896747/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1473/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2241/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62867/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29497/50000 : ℝ) else (80111/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84457/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1369_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1369_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1369_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77896747/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1473/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2241/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62867/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29497/50000 : ℝ) else (80111/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84457/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1369_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

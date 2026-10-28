-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1294_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:27:01.309721+00:00
-- url     : https://prove2.me/submissions/3ee95ad8-2103-472a-be55-2f7aee3f24df

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
theorem support_rectangle_w1294_s0_0 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1837865779/10000000000 : ℝ)*x 0 + (1203581477/2000000000 : ℝ)*x 1 + (2399664111/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1837865779/10000000000 : ℝ)^2127 ≤ (10741891567353/100000000000000 : ℝ)^1615 := by
    have hnat : (1837865779 : ℕ)^2127*100000000000000^1615 ≤ 10741891567353^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1837865779 10000000000 10741891567353 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1203581477/2000000000 : ℝ)^2127 ≤ (51229908197241/100000000000000 : ℝ)^1615 := by
    have hnat : (1203581477 : ℕ)^2127*100000000000000^1615 ≤ 51229908197241^1615*2000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203581477 2000000000 51229908197241 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2399664111/5000000000 : ℝ)^2127 ≤ (2376762513311/6250000000000 : ℝ)^1615 := by
    have hnat : (2399664111 : ℕ)^2127*6250000000000^1615 ≤ 2376762513311^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2399664111 5000000000 2376762513311 6250000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1837865779/10000000000 : ℝ), (1203581477/2000000000 : ℝ), (2399664111/5000000000 : ℝ)] ![(10741891567353/100000000000000 : ℝ), (51229908197241/100000000000000 : ℝ), (2376762513311/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1837865779/10000000000 : ℝ)|^2127 ≤ (10741891567353/100000000000000 : ℝ)^1615
        have hw : |(-1837865779/10000000000 : ℝ)|=(1837865779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1203581477/2000000000 : ℝ)|^2127 ≤ (51229908197241/100000000000000 : ℝ)^1615
        have hw : |(1203581477/2000000000 : ℝ)|=(1203581477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2399664111/5000000000 : ℝ)|^2127 ≤ (2376762513311/6250000000000 : ℝ)^1615
        have hw : |(2399664111/5000000000 : ℝ)|=(2399664111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s0_1 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2753597169/5000000000 : ℝ)*x 0 + (-2532953603/10000000000 : ℝ)*x 1 + (4799328231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2753597169/5000000000 : ℝ)^2127 ≤ (45582497934927/100000000000000 : ℝ)^1615 := by
    have hnat : (2753597169 : ℕ)^2127*100000000000000^1615 ≤ 45582497934927^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2753597169 5000000000 45582497934927 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2532953603/10000000000 : ℝ)^2127 ≤ (1638930173777/10000000000000 : ℝ)^1615 := by
    have hnat : (2532953603 : ℕ)^2127*10000000000000^1615 ≤ 1638930173777^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2532953603 10000000000 1638930173777 10000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4799328231/10000000000 : ℝ)^2127 ≤ (38028200306897/100000000000000 : ℝ)^1615 := by
    have hnat : (4799328231 : ℕ)^2127*100000000000000^1615 ≤ 38028200306897^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4799328231 10000000000 38028200306897 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2753597169/5000000000 : ℝ), (-2532953603/10000000000 : ℝ), (4799328231/10000000000 : ℝ)] ![(45582497934927/100000000000000 : ℝ), (1638930173777/10000000000000 : ℝ), (38028200306897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2753597169/5000000000 : ℝ)|^2127 ≤ (45582497934927/100000000000000 : ℝ)^1615
        have hw : |(2753597169/5000000000 : ℝ)|=(2753597169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2532953603/10000000000 : ℝ)|^2127 ≤ (1638930173777/10000000000000 : ℝ)^1615
        have hw : |(-2532953603/10000000000 : ℝ)|=(2532953603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4799328231/10000000000 : ℝ)|^2127 ≤ (38028200306897/100000000000000 : ℝ)^1615
        have hw : |(4799328231/10000000000 : ℝ)|=(4799328231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s0_2 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5507194017/10000000000 : ℝ)*x 0 + (4799328663/10000000000 : ℝ)*x 1 + (-506590697/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5507194017/10000000000 : ℝ)^2127 ≤ (9116498887147/20000000000000 : ℝ)^1615 := by
    have hnat : (5507194017 : ℕ)^2127*20000000000000^1615 ≤ 9116498887147^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5507194017 10000000000 9116498887147 20000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4799328663/10000000000 : ℝ)^2127 ≤ (19014102407553/50000000000000 : ℝ)^1615 := by
    have hnat : (4799328663 : ℕ)^2127*50000000000000^1615 ≤ 19014102407553^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4799328663 10000000000 19014102407553 50000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (506590697/2000000000 : ℝ)^2127 ≤ (3277860146441/20000000000000 : ℝ)^1615 := by
    have hnat : (506590697 : ℕ)^2127*20000000000000^1615 ≤ 3277860146441^1615*2000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506590697 2000000000 3277860146441 20000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5507194017/10000000000 : ℝ), (4799328663/10000000000 : ℝ), (-506590697/2000000000 : ℝ)] ![(9116498887147/20000000000000 : ℝ), (19014102407553/50000000000000 : ℝ), (3277860146441/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5507194017/10000000000 : ℝ)|^2127 ≤ (9116498887147/20000000000000 : ℝ)^1615
        have hw : |(5507194017/10000000000 : ℝ)|=(5507194017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4799328663/10000000000 : ℝ)|^2127 ≤ (19014102407553/50000000000000 : ℝ)^1615
        have hw : |(4799328663/10000000000 : ℝ)|=(4799328663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-506590697/2000000000 : ℝ)|^2127 ≤ (3277860146441/20000000000000 : ℝ)^1615
        have hw : |(-506590697/2000000000 : ℝ)|=(506590697/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s0_3 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4186024687/10000000000 : ℝ)*x 0 + (777325981/2500000000 : ℝ)*x 1 + (1403921471/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4186024687/10000000000 : ℝ)^2127 ≤ (31761603007921/100000000000000 : ℝ)^1615 := by
    have hnat : (4186024687 : ℕ)^2127*100000000000000^1615 ≤ 31761603007921^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4186024687 10000000000 31761603007921 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (777325981/2500000000 : ℝ)^2127 ≤ (21469565983701/100000000000000 : ℝ)^1615 := by
    have hnat : (777325981 : ℕ)^2127*100000000000000^1615 ≤ 21469565983701^1615*2500000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      777325981 2500000000 21469565983701 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1403921471/2500000000 : ℝ)^2127 ≤ (46768830994277/100000000000000 : ℝ)^1615 := by
    have hnat : (1403921471 : ℕ)^2127*100000000000000^1615 ≤ 46768830994277^1615*2500000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1403921471 2500000000 46768830994277 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4186024687/10000000000 : ℝ), (777325981/2500000000 : ℝ), (1403921471/2500000000 : ℝ)] ![(31761603007921/100000000000000 : ℝ), (21469565983701/100000000000000 : ℝ), (46768830994277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4186024687/10000000000 : ℝ)|^2127 ≤ (31761603007921/100000000000000 : ℝ)^1615
        have hw : |(4186024687/10000000000 : ℝ)|=(4186024687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(777325981/2500000000 : ℝ)|^2127 ≤ (21469565983701/100000000000000 : ℝ)^1615
        have hw : |(777325981/2500000000 : ℝ)|=(777325981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1403921471/2500000000 : ℝ)|^2127 ≤ (46768830994277/100000000000000 : ℝ)^1615
        have hw : |(1403921471/2500000000 : ℝ)|=(1403921471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s0_4 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1842578357/10000000000 : ℝ)*x 0 + (4830776527/10000000000 : ℝ)*x 1 + (598534073/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1842578357/10000000000 : ℝ)^2127 ≤ (84204549959/781250000000 : ℝ)^1615 := by
    have hnat : (1842578357 : ℕ)^2127*781250000000^1615 ≤ 84204549959^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1842578357 10000000000 84204549959 781250000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4830776527/10000000000 : ℝ)^2127 ≤ (38356724678087/100000000000000 : ℝ)^1615 := by
    have hnat : (4830776527 : ℕ)^2127*100000000000000^1615 ≤ 38356724678087^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4830776527 10000000000 38356724678087 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (598534073/1000000000 : ℝ)^2127 ≤ (50865092910023/100000000000000 : ℝ)^1615 := by
    have hnat : (598534073 : ℕ)^2127*100000000000000^1615 ≤ 50865092910023^1615*1000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598534073 1000000000 50865092910023 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1842578357/10000000000 : ℝ), (4830776527/10000000000 : ℝ), (598534073/1000000000 : ℝ)] ![(84204549959/781250000000 : ℝ), (38356724678087/100000000000000 : ℝ), (50865092910023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1842578357/10000000000 : ℝ)|^2127 ≤ (84204549959/781250000000 : ℝ)^1615
        have hw : |(-1842578357/10000000000 : ℝ)|=(1842578357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4830776527/10000000000 : ℝ)|^2127 ≤ (38356724678087/100000000000000 : ℝ)^1615
        have hw : |(4830776527/10000000000 : ℝ)|=(4830776527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(598534073/1000000000 : ℝ)|^2127 ≤ (50865092910023/100000000000000 : ℝ)^1615
        have hw : |(598534073/1000000000 : ℝ)|=(598534073/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s0_5 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (517542939/1000000000 : ℝ)*x 0 + (-1346938799/10000000000 : ℝ)*x 1 + (1496335843/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (517542939/1000000000 : ℝ)^2127 ≤ (2100048991831/5000000000000 : ℝ)^1615 := by
    have hnat : (517542939 : ℕ)^2127*5000000000000^1615 ≤ 2100048991831^1615*1000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517542939 1000000000 2100048991831 5000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1346938799/10000000000 : ℝ)^2127 ≤ (1426779535923/20000000000000 : ℝ)^1615 := by
    have hnat : (1346938799 : ℕ)^2127*20000000000000^1615 ≤ 1426779535923^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346938799 10000000000 1426779535923 20000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1496335843/2500000000 : ℝ)^2127 ≤ (5086512248053/10000000000000 : ℝ)^1615 := by
    have hnat : (1496335843 : ℕ)^2127*10000000000000^1615 ≤ 5086512248053^1615*2500000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1496335843 2500000000 5086512248053 10000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(517542939/1000000000 : ℝ), (-1346938799/10000000000 : ℝ), (1496335843/2500000000 : ℝ)] ![(2100048991831/5000000000000 : ℝ), (1426779535923/20000000000000 : ℝ), (5086512248053/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(517542939/1000000000 : ℝ)|^2127 ≤ (2100048991831/5000000000000 : ℝ)^1615
        have hw : |(517542939/1000000000 : ℝ)|=(517542939/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1346938799/10000000000 : ℝ)|^2127 ≤ (1426779535923/20000000000000 : ℝ)^1615
        have hw : |(-1346938799/10000000000 : ℝ)|=(1346938799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1496335843/2500000000 : ℝ)|^2127 ≤ (5086512248053/10000000000000 : ℝ)^1615
        have hw : |(1496335843/2500000000 : ℝ)|=(1496335843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s0_6 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1293857673/2500000000 : ℝ)*x 0 + (748167639/1250000000 : ℝ)*x 1 + (-1346940429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1293857673/2500000000 : ℝ)^2127 ≤ (42000993752767/100000000000000 : ℝ)^1615 := by
    have hnat : (1293857673 : ℕ)^2127*100000000000000^1615 ≤ 42000993752767^1615*2500000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293857673 2500000000 42000993752767 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (748167639/1250000000 : ℝ)^2127 ≤ (50865097185547/100000000000000 : ℝ)^1615 := by
    have hnat : (748167639 : ℕ)^2127*100000000000000^1615 ≤ 50865097185547^1615*1250000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      748167639 1250000000 50865097185547 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346940429/10000000000 : ℝ)^2127 ≤ (3566954524823/50000000000000 : ℝ)^1615 := by
    have hnat : (1346940429 : ℕ)^2127*50000000000000^1615 ≤ 3566954524823^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346940429 10000000000 3566954524823 50000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1293857673/2500000000 : ℝ), (748167639/1250000000 : ℝ), (-1346940429/10000000000 : ℝ)] ![(42000993752767/100000000000000 : ℝ), (50865097185547/100000000000000 : ℝ), (3566954524823/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1293857673/2500000000 : ℝ)|^2127 ≤ (42000993752767/100000000000000 : ℝ)^1615
        have hw : |(1293857673/2500000000 : ℝ)|=(1293857673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(748167639/1250000000 : ℝ)|^2127 ≤ (50865097185547/100000000000000 : ℝ)^1615
        have hw : |(748167639/1250000000 : ℝ)|=(748167639/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1346940429/10000000000 : ℝ)|^2127 ≤ (3566954524823/50000000000000 : ℝ)^1615
        have hw : |(-1346940429/10000000000 : ℝ)|=(1346940429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s0_7 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (419572233/1000000000 : ℝ)*x 0 + (5551011137/10000000000 : ℝ)*x 1 + (1588139707/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419572233/1000000000 : ℝ)^2127 ≤ (15929273528371/50000000000000 : ℝ)^1615 := by
    have hnat : (419572233 : ℕ)^2127*50000000000000^1615 ≤ 15929273528371^1615*1000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419572233 1000000000 15929273528371 50000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5551011137/10000000000 : ℝ)^2127 ≤ (1439398192037/3125000000000 : ℝ)^1615 := by
    have hnat : (5551011137 : ℕ)^2127*3125000000000^1615 ≤ 1439398192037^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5551011137 10000000000 1439398192037 3125000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1588139707/5000000000 : ℝ)^2127 ≤ (22080710782189/100000000000000 : ℝ)^1615 := by
    have hnat : (1588139707 : ℕ)^2127*100000000000000^1615 ≤ 22080710782189^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1588139707 5000000000 22080710782189 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(419572233/1000000000 : ℝ), (5551011137/10000000000 : ℝ), (1588139707/5000000000 : ℝ)] ![(15929273528371/50000000000000 : ℝ), (1439398192037/3125000000000 : ℝ), (22080710782189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(419572233/1000000000 : ℝ)|^2127 ≤ (15929273528371/50000000000000 : ℝ)^1615
        have hw : |(419572233/1000000000 : ℝ)|=(419572233/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5551011137/10000000000 : ℝ)|^2127 ≤ (1439398192037/3125000000000 : ℝ)^1615
        have hw : |(5551011137/10000000000 : ℝ)|=(5551011137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1588139707/5000000000 : ℝ)|^2127 ≤ (22080710782189/100000000000000 : ℝ)^1615
        have hw : |(1588139707/5000000000 : ℝ)|=(1588139707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1294_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152840397/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (131/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27221/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4253/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4253 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4253*1^1024 ≤ 0^1024*1^4253 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4253 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4253/1024 : ℝ) ≤ (2224475766152526007/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4253 ≤ (2224475766152526007/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4253*100000000000000000000^1024 ≤ 2224475766152526007^1024*5^4253 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2224475766152526007 100000000000000000000 4253 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2224475766152526007/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4253/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4253 := by
      have hnat : (1 : ℕ)^1024*1^4253 ≤ 1^4253*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102224475766152526007/100000000000000000000 : ℝ) ≤ (5026556255069733/5000000000000000 : ℝ) ^ (4253/1024 : ℝ) := by
    have hpowers : (102224475766152526007/100000000000000000000 : ℝ)^1024 ≤ (5026556255069733/5000000000000000 : ℝ)^4253 := by
      have hnat : (102224475766152526007 : ℕ)^1024*5000000000000000^4253 ≤ 5026556255069733^4253*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102224475766152526007 100000000000000000000 5026556255069733 5000000000000000 1024 4253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5026556255069733/5000000000000000 : ℝ)) (X := (102224475766152526007/100000000000000000000 : ℝ)) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52224475766152526007/50000000000000000000 : ℝ) ≤ (2526556255069733/2500000000000000 : ℝ) ^ (4253/1024 : ℝ) := by
    have hpowers : (52224475766152526007/50000000000000000000 : ℝ)^1024 ≤ (2526556255069733/2500000000000000 : ℝ)^4253 := by
      have hnat : (52224475766152526007 : ℕ)^1024*2500000000000000^4253 ≤ 2526556255069733^4253*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52224475766152526007 50000000000000000000 2526556255069733 2500000000000000 1024 4253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2526556255069733/2500000000000000 : ℝ)) (X := (52224475766152526007/50000000000000000000 : ℝ)) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(26556255069733/2000000000000000 : ℝ)*(0 : ℝ))^(4253/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(26556255069733/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2224475766152526007/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(26556255069733/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4253/1024 : ℝ) := by
    rw [show (1 : ℝ)+(26556255069733/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5026556255069733/5000000000000000 : ℝ) by norm_num, show 1+(2224475766152526007/100000000000000000000 : ℝ)+(0 : ℝ)=(102224475766152526007/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2224475766152526007/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(26556255069733/2000000000000000 : ℝ)*(2/5 : ℝ))^(4253/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(26556255069733/2000000000000000 : ℝ)*(2/5 : ℝ)=(2526556255069733/2500000000000000 : ℝ) by norm_num, show 1+2*(2224475766152526007/100000000000000000000 : ℝ)=(52224475766152526007/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(26556255069733/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4253/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (26556255069733/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(26556255069733/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4253/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (26556255069733/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(26556255069733/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4253/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (26556255069733/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1837865779/10000000000 : ℝ)*X 0 0+(1203581477/2000000000 : ℝ)*X 0 1+(2399664111/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2753597169/5000000000 : ℝ)*X 1 0+(-2532953603/10000000000 : ℝ)*X 1 1+(4799328231/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5507194017/10000000000 : ℝ)*X 2 0+(4799328663/10000000000 : ℝ)*X 2 1+(-506590697/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4186024687/10000000000 : ℝ)*X 0 0+(777325981/2500000000 : ℝ)*X 0 1+(1403921471/2500000000 : ℝ)*X 0 2+(4186024687/10000000000 : ℝ)*X 1 0+(777325981/2500000000 : ℝ)*X 1 1+(1403921471/2500000000 : ℝ)*X 1 2+(4186024687/10000000000 : ℝ)*X 2 0+(777325981/2500000000 : ℝ)*X 2 1+(1403921471/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1842578357/10000000000 : ℝ)*X 0 0+(4830776527/10000000000 : ℝ)*X 0 1+(598534073/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((517542939/1000000000 : ℝ)*X 1 0+(-1346938799/10000000000 : ℝ)*X 1 1+(1496335843/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1293857673/2500000000 : ℝ)*X 2 0+(748167639/1250000000 : ℝ)*X 2 1+(-1346940429/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((419572233/1000000000 : ℝ)*X 0 0+(5551011137/10000000000 : ℝ)*X 0 1+(1588139707/5000000000 : ℝ)*X 0 2+(419572233/1000000000 : ℝ)*X 1 0+(5551011137/10000000000 : ℝ)*X 1 1+(1588139707/5000000000 : ℝ)*X 1 2+(419572233/1000000000 : ℝ)*X 2 0+(5551011137/10000000000 : ℝ)*X 2 1+(1588139707/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (44798916145111913406639/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (95971259/100000000000000 : ℝ)*(base1) + (480567809/50000000000000 : ℝ)*(base19) + (913303077/100000000000000 : ℝ)*(base23) + (96290901/100000000000000 : ℝ)*(upper3) + (13732801/12500000000000 : ℝ)*(upper5) + (152452233179561/25000000000000 : ℝ)*(major0) + (152452233179561/25000000000000 : ℝ)*(major1) + (152452233179561/25000000000000 : ℝ)*(major2) + (164126137691919/20000000000000 : ℝ)*(sp0) + (51289540744969/6250000000000 : ℝ)*(sp1) + (205158174938011/25000000000000 : ℝ)*(sp2) + (199491380043837/50000000000000 : ℝ)*(sp3) + (1510283393/50000000000000 : ℝ)*(sp4) + (319214663/25000000000000 : ℝ)*(sp7) + (79796826583517/20000000000000 : ℝ)*(f.failure) + (410316806527561/50000000000000 : ℝ)*(f.sum) + (27398561947787/25000000000000000000000000000 : ℝ)*base66 + (568133704522787/50000000000000000000000000000 : ℝ)*base68 + (117241984627213/50000000000000000000000000000 : ℝ)*base69 + (33673412172787/50000000000000000000000000000 : ℝ)*base72 + (177126314372787/25000000000000000000000000000 : ℝ)*base74 + (181034693072787/50000000000000000000000000000 : ℝ)*base76 + (124338968027213/50000000000000000000000000000 : ℝ)*base77 + (2773498272787/50000000000000000000000000000 : ℝ)*base80 + (35932605227213/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (11936249/2000000000000000000000 : ℝ)*base89 + (11936249/2000000000000000000000 : ℝ)*base91 + (11936249/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (423450839487148546900929/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (482063013/100000000000000 : ℝ)*(base1) + (413403197/25000000000000 : ℝ)*(base19) + (932325799/50000000000000 : ℝ)*(base23) + (165340521/50000000000000 : ℝ)*(upper3) + (643613610469243/100000000000000 : ℝ)*(major0) + (643613610469243/100000000000000 : ℝ)*(major1) + (643613610469243/100000000000000 : ℝ)*(major2) + (1152965229/50000000000000 : ℝ)*(sp1) + (219900983/10000000000000 : ℝ)*(sp2) + (55468629/100000000000000 : ℝ)*(sp3) + (216531413750339/25000000000000 : ℝ)*(sp4) + (866121213395097/100000000000000 : ℝ)*(sp5) + (216530277319229/25000000000000 : ℝ)*(sp6) + (210550614083967/50000000000000 : ℝ)*(sp7) + (421101765699577/100000000000000 : ℝ)*(f.failure) + (866125172938343/100000000000000 : ℝ)*(f.sum) + (129607991622119/100000000000000000000000000000 : ℝ)*base65 + (1341293463522119/200000000000000000000000000000 : ℝ)*base67 + (1624409098322119/200000000000000000000000000000 : ℝ)*base69 + (2027292221322119/200000000000000000000000000000 : ℝ)*base71 + (92196569022119/100000000000000000000000000000 : ℝ)*base73 + (1029133697922119/200000000000000000000000000000 : ℝ)*base75 + (571563151722119/200000000000000000000000000000 : ℝ)*base77 + (31862009522119/200000000000000000000000000000 : ℝ)*base79 + (493198896922119/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (31412069/10000000000000000000000 : ℝ)*base89 + (31412069/10000000000000000000000 : ℝ)*base91 + (31412069/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1294_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152840397/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (131/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27221/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1294_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1294_s1_0 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2029616777/10000000000 : ℝ)*x 0 + (1132872911/2000000000 : ℝ)*x 1 + (5030108887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2029616777/10000000000 : ℝ)^2127 ≤ (12241792054747/100000000000000 : ℝ)^1615 := by
    have hnat : (2029616777 : ℕ)^2127*100000000000000^1615 ≤ 12241792054747^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2029616777 10000000000 12241792054747 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1132872911/2000000000 : ℝ)^2127 ≤ (11825874241737/25000000000000 : ℝ)^1615 := by
    have hnat : (1132872911 : ℕ)^2127*25000000000000^1615 ≤ 11825874241737^1615*2000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132872911 2000000000 11825874241737 25000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5030108887/10000000000 : ℝ)^2127 ≤ (40454710965693/100000000000000 : ℝ)^1615 := by
    have hnat : (5030108887 : ℕ)^2127*100000000000000^1615 ≤ 40454710965693^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5030108887 10000000000 40454710965693 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2029616777/10000000000 : ℝ), (1132872911/2000000000 : ℝ), (5030108887/10000000000 : ℝ)] ![(12241792054747/100000000000000 : ℝ), (11825874241737/25000000000000 : ℝ), (40454710965693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2029616777/10000000000 : ℝ)|^2127 ≤ (12241792054747/100000000000000 : ℝ)^1615
        have hw : |(-2029616777/10000000000 : ℝ)|=(2029616777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1132872911/2000000000 : ℝ)|^2127 ≤ (11825874241737/25000000000000 : ℝ)^1615
        have hw : |(1132872911/2000000000 : ℝ)|=(1132872911/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5030108887/10000000000 : ℝ)|^2127 ≤ (40454710965693/100000000000000 : ℝ)^1615
        have hw : |(5030108887/10000000000 : ℝ)|=(5030108887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s1_1 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5410775701/10000000000 : ℝ)*x 0 + (-236950679/1000000000 : ℝ)*x 1 + (314381807/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5410775701/10000000000 : ℝ)^2127 ≤ (44534375838459/100000000000000 : ℝ)^1615 := by
    have hnat : (5410775701 : ℕ)^2127*100000000000000^1615 ≤ 44534375838459^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410775701 10000000000 44534375838459 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (236950679/1000000000 : ℝ)^2127 ≤ (15010912924079/100000000000000 : ℝ)^1615 := by
    have hnat : (236950679 : ℕ)^2127*100000000000000^1615 ≤ 15010912924079^1615*1000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236950679 1000000000 15010912924079 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (314381807/625000000 : ℝ)^2127 ≤ (40454711230499/100000000000000 : ℝ)^1615 := by
    have hnat : (314381807 : ℕ)^2127*100000000000000^1615 ≤ 40454711230499^1615*625000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314381807 625000000 40454711230499 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5410775701/10000000000 : ℝ), (-236950679/1000000000 : ℝ), (314381807/625000000 : ℝ)] ![(44534375838459/100000000000000 : ℝ), (15010912924079/100000000000000 : ℝ), (40454711230499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5410775701/10000000000 : ℝ)|^2127 ≤ (44534375838459/100000000000000 : ℝ)^1615
        have hw : |(5410775701/10000000000 : ℝ)|=(5410775701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-236950679/1000000000 : ℝ)|^2127 ≤ (15010912924079/100000000000000 : ℝ)^1615
        have hw : |(-236950679/1000000000 : ℝ)|=(236950679/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(314381807/625000000 : ℝ)|^2127 ≤ (40454711230499/100000000000000 : ℝ)^1615
        have hw : |(314381807/625000000 : ℝ)|=(314381807/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s1_2 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (8657241/16000000 : ℝ)*x 0 + (5030108871/10000000000 : ℝ)*x 1 + (-2369506939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8657241/16000000 : ℝ)^2127 ≤ (5566796876827/12500000000000 : ℝ)^1615 := by
    have hnat : (8657241 : ℕ)^2127*12500000000000^1615 ≤ 5566796876827^1615*16000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8657241 16000000 5566796876827 12500000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5030108871/10000000000 : ℝ)^2127 ≤ (20227355398109/50000000000000 : ℝ)^1615 := by
    have hnat : (5030108871 : ℕ)^2127*50000000000000^1615 ≤ 20227355398109^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5030108871 10000000000 20227355398109 50000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2369506939/10000000000 : ℝ)^2127 ≤ (15010914167249/100000000000000 : ℝ)^1615 := by
    have hnat : (2369506939 : ℕ)^2127*100000000000000^1615 ≤ 15010914167249^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2369506939 10000000000 15010914167249 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8657241/16000000 : ℝ), (5030108871/10000000000 : ℝ), (-2369506939/10000000000 : ℝ)] ![(5566796876827/12500000000000 : ℝ), (20227355398109/50000000000000 : ℝ), (15010914167249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8657241/16000000 : ℝ)|^2127 ≤ (5566796876827/12500000000000 : ℝ)^1615
        have hw : |(8657241/16000000 : ℝ)|=(8657241/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5030108871/10000000000 : ℝ)|^2127 ≤ (20227355398109/50000000000000 : ℝ)^1615
        have hw : |(5030108871/10000000000 : ℝ)|=(5030108871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2369506939/10000000000 : ℝ)|^2127 ≤ (15010914167249/100000000000000 : ℝ)^1615
        have hw : |(-2369506939/10000000000 : ℝ)|=(2369506939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s1_3 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1075197111/2500000000 : ℝ)*x 0 + (57739613/156250000 : ℝ)*x 1 + (4999876863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075197111/2500000000 : ℝ)^2127 ≤ (32913389612573/100000000000000 : ℝ)^1615 := by
    have hnat : (1075197111 : ℕ)^2127*100000000000000^1615 ≤ 32913389612573^1615*2500000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075197111 2500000000 32913389612573 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (57739613/156250000 : ℝ)^2127 ≤ (26951817920977/100000000000000 : ℝ)^1615 := by
    have hnat : (57739613 : ℕ)^2127*100000000000000^1615 ≤ 26951817920977^1615*156250000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57739613 156250000 26951817920977 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4999876863/10000000000 : ℝ)^2127 ≤ (10033698110969/25000000000000 : ℝ)^1615 := by
    have hnat : (4999876863 : ℕ)^2127*25000000000000^1615 ≤ 10033698110969^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4999876863 10000000000 10033698110969 25000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075197111/2500000000 : ℝ), (57739613/156250000 : ℝ), (4999876863/10000000000 : ℝ)] ![(32913389612573/100000000000000 : ℝ), (26951817920977/100000000000000 : ℝ), (10033698110969/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075197111/2500000000 : ℝ)|^2127 ≤ (32913389612573/100000000000000 : ℝ)^1615
        have hw : |(1075197111/2500000000 : ℝ)|=(1075197111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(57739613/156250000 : ℝ)|^2127 ≤ (26951817920977/100000000000000 : ℝ)^1615
        have hw : |(57739613/156250000 : ℝ)|=(57739613/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4999876863/10000000000 : ℝ)|^2127 ≤ (10033698110969/25000000000000 : ℝ)^1615
        have hw : |(4999876863/10000000000 : ℝ)|=(4999876863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s1_4 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2030249543/10000000000 : ℝ)*x 0 + (1007673157/2000000000 : ℝ)*x 1 + (2827975823/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2030249543/10000000000 : ℝ)^2127 ≤ (3061704710523/25000000000000 : ℝ)^1615 := by
    have hnat : (2030249543 : ℕ)^2127*25000000000000^1615 ≤ 3061704710523^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2030249543 10000000000 3061704710523 25000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1007673157/2000000000 : ℝ)^2127 ≤ (1621687701243/4000000000000 : ℝ)^1615 := by
    have hnat : (1007673157 : ℕ)^2127*4000000000000^1615 ≤ 1621687701243^1615*2000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007673157 2000000000 1621687701243 4000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2827975823/5000000000 : ℝ)^2127 ≤ (11802747155403/25000000000000 : ℝ)^1615 := by
    have hnat : (2827975823 : ℕ)^2127*25000000000000^1615 ≤ 11802747155403^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2827975823 5000000000 11802747155403 25000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2030249543/10000000000 : ℝ), (1007673157/2000000000 : ℝ), (2827975823/5000000000 : ℝ)] ![(3061704710523/25000000000000 : ℝ), (1621687701243/4000000000000 : ℝ), (11802747155403/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2030249543/10000000000 : ℝ)|^2127 ≤ (3061704710523/25000000000000 : ℝ)^1615
        have hw : |(-2030249543/10000000000 : ℝ)|=(2030249543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1007673157/2000000000 : ℝ)|^2127 ≤ (1621687701243/4000000000000 : ℝ)^1615
        have hw : |(1007673157/2000000000 : ℝ)|=(1007673157/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2827975823/5000000000 : ℝ)|^2127 ≤ (11802747155403/25000000000000 : ℝ)^1615
        have hw : |(2827975823/5000000000 : ℝ)|=(2827975823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s1_5 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1049375281/2000000000 : ℝ)*x 0 + (-1743663651/10000000000 : ℝ)*x 1 + (2827976163/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049375281/2000000000 : ℝ)^2127 ≤ (42766291704419/100000000000000 : ℝ)^1615 := by
    have hnat : (1049375281 : ℕ)^2127*100000000000000^1615 ≤ 42766291704419^1615*2000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049375281 2000000000 42766291704419 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1743663651/10000000000 : ℝ)^2127 ≤ (2004542435463/20000000000000 : ℝ)^1615 := by
    have hnat : (1743663651 : ℕ)^2127*20000000000000^1615 ≤ 2004542435463^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1743663651 10000000000 2004542435463 20000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2827976163/5000000000 : ℝ)^2127 ≤ (4721099609713/10000000000000 : ℝ)^1615 := by
    have hnat : (2827976163 : ℕ)^2127*10000000000000^1615 ≤ 4721099609713^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2827976163 5000000000 4721099609713 10000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1049375281/2000000000 : ℝ), (-1743663651/10000000000 : ℝ), (2827976163/5000000000 : ℝ)] ![(42766291704419/100000000000000 : ℝ), (2004542435463/20000000000000 : ℝ), (4721099609713/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1049375281/2000000000 : ℝ)|^2127 ≤ (42766291704419/100000000000000 : ℝ)^1615
        have hw : |(1049375281/2000000000 : ℝ)|=(1049375281/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1743663651/10000000000 : ℝ)|^2127 ≤ (2004542435463/20000000000000 : ℝ)^1615
        have hw : |(-1743663651/10000000000 : ℝ)|=(1743663651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2827976163/5000000000 : ℝ)|^2127 ≤ (4721099609713/10000000000000 : ℝ)^1615
        have hw : |(2827976163/5000000000 : ℝ)|=(2827976163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s1_6 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1049375263/2000000000 : ℝ)*x 0 + (5655951927/10000000000 : ℝ)*x 1 + (-1743664359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049375263/2000000000 : ℝ)^2127 ≤ (42766290738283/100000000000000 : ℝ)^1615 := by
    have hnat : (1049375263 : ℕ)^2127*100000000000000^1615 ≤ 42766290738283^1615*2000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049375263 2000000000 42766290738283 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5655951927/10000000000 : ℝ)^2127 ≤ (1180274792769/2500000000000 : ℝ)^1615 := by
    have hnat : (5655951927 : ℕ)^2127*2500000000000^1615 ≤ 1180274792769^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5655951927 10000000000 1180274792769 2500000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1743664359/10000000000 : ℝ)^2127 ≤ (10022717537143/100000000000000 : ℝ)^1615 := by
    have hnat : (1743664359 : ℕ)^2127*100000000000000^1615 ≤ 10022717537143^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1743664359 10000000000 10022717537143 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1049375263/2000000000 : ℝ), (5655951927/10000000000 : ℝ), (-1743664359/10000000000 : ℝ)] ![(42766290738283/100000000000000 : ℝ), (1180274792769/2500000000000 : ℝ), (10022717537143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1049375263/2000000000 : ℝ)|^2127 ≤ (42766290738283/100000000000000 : ℝ)^1615
        have hw : |(1049375263/2000000000 : ℝ)|=(1049375263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5655951927/10000000000 : ℝ)|^2127 ≤ (1180274792769/2500000000000 : ℝ)^1615
        have hw : |(5655951927/10000000000 : ℝ)|=(5655951927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1743664359/10000000000 : ℝ)|^2127 ≤ (10022717537143/100000000000000 : ℝ)^1615
        have hw : |(-1743664359/10000000000 : ℝ)|=(1743664359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s1_7 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1075522293/2500000000 : ℝ)*x 0 + (2491447259/5000000000 : ℝ)*x 1 + (5940221/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075522293/2500000000 : ℝ)^2127 ≤ (8231625085099/25000000000000 : ℝ)^1615 := by
    have hnat : (1075522293 : ℕ)^2127*25000000000000^1615 ≤ 8231625085099^1615*2500000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075522293 2500000000 8231625085099 25000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2491447259/5000000000 : ℝ)^2127 ≤ (39955352028171/100000000000000 : ℝ)^1615 := by
    have hnat : (2491447259 : ℕ)^2127*100000000000000^1615 ≤ 39955352028171^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2491447259 5000000000 39955352028171 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5940221/16000000 : ℝ)^2127 ≤ (13559073807053/50000000000000 : ℝ)^1615 := by
    have hnat : (5940221 : ℕ)^2127*50000000000000^1615 ≤ 13559073807053^1615*16000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5940221 16000000 13559073807053 50000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075522293/2500000000 : ℝ), (2491447259/5000000000 : ℝ), (5940221/16000000 : ℝ)] ![(8231625085099/25000000000000 : ℝ), (39955352028171/100000000000000 : ℝ), (13559073807053/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075522293/2500000000 : ℝ)|^2127 ≤ (8231625085099/25000000000000 : ℝ)^1615
        have hw : |(1075522293/2500000000 : ℝ)|=(1075522293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2491447259/5000000000 : ℝ)|^2127 ≤ (39955352028171/100000000000000 : ℝ)^1615
        have hw : |(2491447259/5000000000 : ℝ)|=(2491447259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5940221/16000000 : ℝ)|^2127 ≤ (13559073807053/50000000000000 : ℝ)^1615
        have hw : |(5940221/16000000 : ℝ)|=(5940221/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1294_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152840397/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27221/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (131/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (1607/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9917/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27221/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (131/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27221/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (131/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27221/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (131/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27221/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (131/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27221/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (131/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27221/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (131/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (131/12500 : ℝ) ^ (4253/1024 : ℝ) ≤ (299844652647/50000000000000000000 : ℝ) := by
    have hpowers : (131/12500 : ℝ)^4253 ≤ (299844652647/50000000000000000000 : ℝ)^1024 := by
      have hnat : (131 : ℕ)^4253*50000000000000000000^1024 ≤ 299844652647^1024*12500^4253 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        131 12500 299844652647 50000000000000000000 4253 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (131/12500 : ℝ)) (X := (299844652647/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (27221/100000 : ℝ) ^ (4253/1024 : ℝ) ≤ (44975460472226409/10000000000000000000 : ℝ) := by
    have hpowers : (27221/100000 : ℝ)^4253 ≤ (44975460472226409/10000000000000000000 : ℝ)^1024 := by
      have hnat : (27221 : ℕ)^4253*10000000000000000000^1024 ≤ 44975460472226409^1024*100000^4253 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27221 100000 44975460472226409 10000000000000000000 4253 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27221/100000 : ℝ)) (X := (44975460472226409/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000299844652647/25000000000000000000 : ℝ) ≤ (5000000014438793/5000000000000000 : ℝ) ^ (4253/1024 : ℝ) := by
    have hpowers : (25000000299844652647/25000000000000000000 : ℝ)^1024 ≤ (5000000014438793/5000000000000000 : ℝ)^4253 := by
      have hnat : (25000000299844652647 : ℕ)^1024*5000000000000000^4253 ≤ 5000000014438793^4253*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000299844652647 25000000000000000000 5000000014438793 5000000000000000 1024 4253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000014438793/5000000000000000 : ℝ)) (X := (25000000299844652647/25000000000000000000 : ℝ)) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12556219400551446173/12500000000000000000 : ℝ) ≤ (2502702592784641/2500000000000000 : ℝ) ^ (4253/1024 : ℝ) := by
    have hpowers : (12556219400551446173/12500000000000000000 : ℝ)^1024 ≤ (2502702592784641/2500000000000000 : ℝ)^4253 := by
      have hnat : (12556219400551446173 : ℕ)^1024*2500000000000000^4253 ≤ 2502702592784641^4253*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12556219400551446173 12500000000000000000 2502702592784641 2500000000000000 1024 4253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502702592784641/2500000000000000 : ℝ)) (X := (12556219400551446173/12500000000000000000 : ℝ)) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5044975460472226409/5000000000000000000 : ℝ) ≤ (5010810356699771/5000000000000000 : ℝ) ^ (4253/1024 : ℝ) := by
    have hpowers : (5044975460472226409/5000000000000000000 : ℝ)^1024 ≤ (5010810356699771/5000000000000000 : ℝ)^4253 := by
      have hnat : (5044975460472226409 : ℕ)^1024*5000000000000000^4253 ≤ 5010810356699771^4253*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5044975460472226409 5000000000000000000 5010810356699771 5000000000000000 1024 4253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5010810356699771/5000000000000000 : ℝ)) (X := (5044975460472226409/5000000000000000000 : ℝ)) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(299844652647/50000000000000000000 : ℝ) ≤ ((26170734227843404849/26173000000000000000 : ℝ)+2*(5405171130489/1308650000000000 : ℝ)*(131/12500 : ℝ))^(4253/1024 : ℝ) := by
    rw [show (26170734227843404849/26173000000000000000 : ℝ)+2*(5405171130489/1308650000000000 : ℝ)*(131/12500 : ℝ)=(5000000014438793/5000000000000000 : ℝ) by norm_num, show 1+2*(299844652647/50000000000000000000 : ℝ)=(25000000299844652647/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(44975460472226409/10000000000000000000 : ℝ)+(299844652647/50000000000000000000 : ℝ) ≤ ((26170734227843404849/26173000000000000000 : ℝ)+(5405171130489/1308650000000000 : ℝ)*((27221/100000 : ℝ)+(131/12500 : ℝ)))^(4253/1024 : ℝ) := by
    rw [show (26170734227843404849/26173000000000000000 : ℝ)+(5405171130489/1308650000000000 : ℝ)*((27221/100000 : ℝ)+(131/12500 : ℝ))=(2502702592784641/2500000000000000 : ℝ) by norm_num, show 1+(44975460472226409/10000000000000000000 : ℝ)+(299844652647/50000000000000000000 : ℝ)=(12556219400551446173/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(44975460472226409/10000000000000000000 : ℝ) ≤ ((26170734227843404849/26173000000000000000 : ℝ)+2*(5405171130489/1308650000000000 : ℝ)*(27221/100000 : ℝ))^(4253/1024 : ℝ) := by
    rw [show (26170734227843404849/26173000000000000000 : ℝ)+2*(5405171130489/1308650000000000 : ℝ)*(27221/100000 : ℝ)=(5010810356699771/5000000000000000 : ℝ) by norm_num, show 1+2*(44975460472226409/10000000000000000000 : ℝ)=(5044975460472226409/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26170734227843404849/26173000000000000000 : ℝ)*(X 1 0+X 2 0)+(5405171130489/1308650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4253/1024 : ℝ)) (lo := (131/12500 : ℝ)) (hi := (27221/100000 : ℝ)) (c := (26170734227843404849/26173000000000000000 : ℝ)) (alpha := (5405171130489/1308650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26170734227843404849/26173000000000000000 : ℝ)*(X 0 1+X 2 1)+(5405171130489/1308650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4253/1024 : ℝ)) (lo := (131/12500 : ℝ)) (hi := (27221/100000 : ℝ)) (c := (26170734227843404849/26173000000000000000 : ℝ)) (alpha := (5405171130489/1308650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26170734227843404849/26173000000000000000 : ℝ)*(X 0 2+X 1 2)+(5405171130489/1308650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4253/1024 : ℝ)) (lo := (131/12500 : ℝ)) (hi := (27221/100000 : ℝ)) (c := (26170734227843404849/26173000000000000000 : ℝ)) (alpha := (5405171130489/1308650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2029616777/10000000000 : ℝ)*X 0 0+(1132872911/2000000000 : ℝ)*X 0 1+(5030108887/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5410775701/10000000000 : ℝ)*X 1 0+(-236950679/1000000000 : ℝ)*X 1 1+(314381807/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((8657241/16000000 : ℝ)*X 2 0+(5030108871/10000000000 : ℝ)*X 2 1+(-2369506939/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1075197111/2500000000 : ℝ)*X 0 0+(57739613/156250000 : ℝ)*X 0 1+(4999876863/10000000000 : ℝ)*X 0 2+(1075197111/2500000000 : ℝ)*X 1 0+(57739613/156250000 : ℝ)*X 1 1+(4999876863/10000000000 : ℝ)*X 1 2+(1075197111/2500000000 : ℝ)*X 2 0+(57739613/156250000 : ℝ)*X 2 1+(4999876863/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2030249543/10000000000 : ℝ)*X 0 0+(1007673157/2000000000 : ℝ)*X 0 1+(2827975823/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1049375281/2000000000 : ℝ)*X 1 0+(-1743663651/10000000000 : ℝ)*X 1 1+(2827976163/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1049375263/2000000000 : ℝ)*X 2 0+(5655951927/10000000000 : ℝ)*X 2 1+(-1743664359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1075522293/2500000000 : ℝ)*X 0 0+(2491447259/5000000000 : ℝ)*X 0 1+(5940221/16000000 : ℝ)*X 0 2+(1075522293/2500000000 : ℝ)*X 1 0+(2491447259/5000000000 : ℝ)*X 1 1+(5940221/16000000 : ℝ)*X 1 2+(1075522293/2500000000 : ℝ)*X 2 0+(2491447259/5000000000 : ℝ)*X 2 1+(5940221/16000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2938973640495049665957301473/327162500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (44471509/50000000000000 : ℝ)*(base1) + (885347627/50000000000000 : ℝ)*(base19) + (437137321/25000000000000 : ℝ)*(base23) + (56800153/25000000000000 : ℝ)*(upper3) + (32741259/20000000000000 : ℝ)*(upper5) + (585808459205659/50000000000000 : ℝ)*(major0) + (585808459205659/50000000000000 : ℝ)*(major1) + (585808459205659/50000000000000 : ℝ)*(major2) + (197082688836091/12500000000000 : ℝ)*(sp0) + (788334715076217/50000000000000 : ℝ)*(sp1) + (315333890459681/20000000000000 : ℝ)*(sp2) + (38327865519807/5000000000000 : ℝ)*(sp3) + (9779101979/100000000000000 : ℝ)*(sp4) + (4937195023/100000000000000 : ℝ)*(sp7) + (766562336534181/100000000000000 : ℝ)*(f.failure) + (1576671200847689/100000000000000 : ℝ)*(f.sum) + (346970419247509/130865000000000000000000000000 : ℝ)*base65 + (3641794526474989509/1308650000000000000000000000000000 : ℝ)*base68 + (16432122057198389509/1308650000000000000000000000000000 : ℝ)*base70 + (218473805256360491/1308650000000000000000000000000000 : ℝ)*base71 + (184065666401047/65432500000000000000000000000 : ℝ)*base73 + (2104313403817089509/1308650000000000000000000000000000 : ℝ)*base76 + (4214148689900789509/1308650000000000000000000000000000 : ℝ)*base78 + (9908953663104989509/1308650000000000000000000000000000 : ℝ)*base80 + (79075341904249/32716250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (28109857/10000000000000000000000 : ℝ)*base89 + (28109857/10000000000000000000000 : ℝ)*base91 + (28109857/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (692950645481823830450213691/186950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (117953403/20000000000000 : ℝ)*(base19) + (299604199/50000000000000 : ℝ)*(base23) + (19292153/50000000000000 : ℝ)*(upper2) + (64978761/50000000000000 : ℝ)*(upper3) + (77113609/100000000000000 : ℝ)*(upper5) + (1203224932643643/100000000000000 : ℝ)*(major0) + (1203224932643643/100000000000000 : ℝ)*(major1) + (1203224932643643/100000000000000 : ℝ)*(major2) + (944110587/25000000000000 : ℝ)*(sp1) + (653418741/25000000000000 : ℝ)*(sp2) + (404801749865173/25000000000000 : ℝ)*(sp4) + (1619202633251329/100000000000000 : ℝ)*(sp5) + (161920378657733/10000000000000 : ℝ)*(sp6) + (98405342784117/12500000000000 : ℝ)*(sp7) + (98405342784117/12500000000000 : ℝ)*(f.failure) + (404801749865173/25000000000000 : ℝ)*(f.sum) + (27947636339551/9347500000000000000000000000 : ℝ)*base65 + (796538420592480701/373900000000000000000000000000000 : ℝ)*base67 + (2800830879652880701/373900000000000000000000000000000 : ℝ)*base69 + (682708634746180701/373900000000000000000000000000000 : ℝ)*base71 + (23466769241433/18695000000000000000000000000 : ℝ)*base74 + (3735787422760680701/373900000000000000000000000000000 : ℝ)*base75 + (2467664887953880701/373900000000000000000000000000000 : ℝ)*base77 + (2796979197409880701/373900000000000000000000000000000 : ℝ)*base79 + (3510706807749/2336875000000000000000000000 : ℝ)*base81 + (9925551/1250000000000000000000 : ℝ)*base90 + (9925551/1250000000000000000000 : ℝ)*base92 + (9925551/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1294_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152840397/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27221/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (131/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1607/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9917/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1294_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1294_s2_0 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-16593029/80000000 : ℝ)*x 0 + (5493642237/10000000000 : ℝ)*x 1 + (323274791/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16593029/80000000 : ℝ)^2127 ≤ (629830323653/5000000000000 : ℝ)^1615 := by
    have hnat : (16593029 : ℕ)^2127*5000000000000^1615 ≤ 629830323653^1615*80000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16593029 80000000 629830323653 5000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5493642237/10000000000 : ℝ)^2127 ≤ (45434825383687/100000000000000 : ℝ)^1615 := by
    have hnat : (5493642237 : ℕ)^2127*100000000000000^1615 ≤ 45434825383687^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5493642237 10000000000 45434825383687 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323274791/625000000 : ℝ)^2127 ≤ (41968568124701/100000000000000 : ℝ)^1615 := by
    have hnat : (323274791 : ℕ)^2127*100000000000000^1615 ≤ 41968568124701^1615*625000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323274791 625000000 41968568124701 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-16593029/80000000 : ℝ), (5493642237/10000000000 : ℝ), (323274791/625000000 : ℝ)] ![(629830323653/5000000000000 : ℝ), (45434825383687/100000000000000 : ℝ), (41968568124701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-16593029/80000000 : ℝ)|^2127 ≤ (629830323653/5000000000000 : ℝ)^1615
        have hw : |(-16593029/80000000 : ℝ)|=(16593029/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5493642237/10000000000 : ℝ)|^2127 ≤ (45434825383687/100000000000000 : ℝ)^1615
        have hw : |(5493642237/10000000000 : ℝ)|=(5493642237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323274791/625000000 : ℝ)|^2127 ≤ (41968568124701/100000000000000 : ℝ)^1615
        have hw : |(323274791/625000000 : ℝ)|=(323274791/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s2_1 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2684717273/5000000000 : ℝ)*x 0 + (-89623361/400000000 : ℝ)*x 1 + (2586198381/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684717273/5000000000 : ℝ)^2127 ≤ (44086779852079/100000000000000 : ℝ)^1615 := by
    have hnat : (2684717273 : ℕ)^2127*100000000000000^1615 ≤ 44086779852079^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684717273 5000000000 44086779852079 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89623361/400000000 : ℝ)^2127 ≤ (6972325434837/50000000000000 : ℝ)^1615 := by
    have hnat : (89623361 : ℕ)^2127*50000000000000^1615 ≤ 6972325434837^1615*400000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89623361 400000000 6972325434837 50000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2586198381/5000000000 : ℝ)^2127 ≤ (5246071157181/12500000000000 : ℝ)^1615 := by
    have hnat : (2586198381 : ℕ)^2127*12500000000000^1615 ≤ 5246071157181^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586198381 5000000000 5246071157181 12500000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684717273/5000000000 : ℝ), (-89623361/400000000 : ℝ), (2586198381/5000000000 : ℝ)] ![(44086779852079/100000000000000 : ℝ), (6972325434837/50000000000000 : ℝ), (5246071157181/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684717273/5000000000 : ℝ)|^2127 ≤ (44086779852079/100000000000000 : ℝ)^1615
        have hw : |(2684717273/5000000000 : ℝ)|=(2684717273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-89623361/400000000 : ℝ)|^2127 ≤ (6972325434837/50000000000000 : ℝ)^1615
        have hw : |(-89623361/400000000 : ℝ)|=(89623361/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2586198381/5000000000 : ℝ)|^2127 ≤ (5246071157181/12500000000000 : ℝ)^1615
        have hw : |(2586198381/5000000000 : ℝ)|=(2586198381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s2_2 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (536943453/1000000000 : ℝ)*x 0 + (2586198331/5000000000 : ℝ)*x 1 + (-1120292089/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536943453/1000000000 : ℝ)^2127 ≤ (44086779679059/100000000000000 : ℝ)^1615 := by
    have hnat : (536943453 : ℕ)^2127*100000000000000^1615 ≤ 44086779679059^1615*1000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536943453 1000000000 44086779679059 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2586198331/5000000000 : ℝ)^2127 ≤ (20984284094409/50000000000000 : ℝ)^1615 := by
    have hnat : (2586198331 : ℕ)^2127*50000000000000^1615 ≤ 20984284094409^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586198331 5000000000 20984284094409 50000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1120292089/5000000000 : ℝ)^2127 ≤ (108942594717/781250000000 : ℝ)^1615 := by
    have hnat : (1120292089 : ℕ)^2127*781250000000^1615 ≤ 108942594717^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120292089 5000000000 108942594717 781250000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536943453/1000000000 : ℝ), (2586198331/5000000000 : ℝ), (-1120292089/5000000000 : ℝ)] ![(44086779679059/100000000000000 : ℝ), (20984284094409/50000000000000 : ℝ), (108942594717/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536943453/1000000000 : ℝ)|^2127 ≤ (44086779679059/100000000000000 : ℝ)^1615
        have hw : |(536943453/1000000000 : ℝ)|=(536943453/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2586198331/5000000000 : ℝ)|^2127 ≤ (20984284094409/50000000000000 : ℝ)^1615
        have hw : |(2586198331/5000000000 : ℝ)|=(2586198331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1120292089/5000000000 : ℝ)|^2127 ≤ (108942594717/781250000000 : ℝ)^1615
        have hw : |(-1120292089/5000000000 : ℝ)|=(1120292089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s2_3 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (866347113/2000000000 : ℝ)*x 0 + (4013355139/10000000000 : ℝ)*x 1 + (2337051577/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (866347113/2000000000 : ℝ)^2127 ≤ (6645132462739/20000000000000 : ℝ)^1615 := by
    have hnat : (866347113 : ℕ)^2127*20000000000000^1615 ≤ 6645132462739^1615*2000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866347113 2000000000 6645132462739 20000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4013355139/10000000000 : ℝ)^2127 ≤ (30047507392187/100000000000000 : ℝ)^1615 := by
    have hnat : (4013355139 : ℕ)^2127*100000000000000^1615 ≤ 30047507392187^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4013355139 10000000000 30047507392187 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2337051577/5000000000 : ℝ)^2127 ≤ (2295426892557/6250000000000 : ℝ)^1615 := by
    have hnat : (2337051577 : ℕ)^2127*6250000000000^1615 ≤ 2295426892557^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2337051577 5000000000 2295426892557 6250000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(866347113/2000000000 : ℝ), (4013355139/10000000000 : ℝ), (2337051577/5000000000 : ℝ)] ![(6645132462739/20000000000000 : ℝ), (30047507392187/100000000000000 : ℝ), (2295426892557/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(866347113/2000000000 : ℝ)|^2127 ≤ (6645132462739/20000000000000 : ℝ)^1615
        have hw : |(866347113/2000000000 : ℝ)|=(866347113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4013355139/10000000000 : ℝ)|^2127 ≤ (30047507392187/100000000000000 : ℝ)^1615
        have hw : |(4013355139/10000000000 : ℝ)|=(4013355139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2337051577/5000000000 : ℝ)|^2127 ≤ (2295426892557/6250000000000 : ℝ)^1615
        have hw : |(2337051577/5000000000 : ℝ)|=(2337051577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s2_4 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2074210099/10000000000 : ℝ)*x 0 + (5174524197/10000000000 : ℝ)*x 1 + (2745747427/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2074210099/10000000000 : ℝ)^2127 ≤ (2519451630669/20000000000000 : ℝ)^1615 := by
    have hnat : (2074210099 : ℕ)^2127*20000000000000^1615 ≤ 2519451630669^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074210099 10000000000 2519451630669 20000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5174524197/10000000000 : ℝ)^2127 ≤ (41991305144723/100000000000000 : ℝ)^1615 := by
    have hnat : (5174524197 : ℕ)^2127*100000000000000^1615 ≤ 41991305144723^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174524197 10000000000 41991305144723 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2745747427/5000000000 : ℝ)^2127 ≤ (45411436685411/100000000000000 : ℝ)^1615 := by
    have hnat : (2745747427 : ℕ)^2127*100000000000000^1615 ≤ 45411436685411^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745747427 5000000000 45411436685411 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2074210099/10000000000 : ℝ), (5174524197/10000000000 : ℝ), (2745747427/5000000000 : ℝ)] ![(2519451630669/20000000000000 : ℝ), (41991305144723/100000000000000 : ℝ), (45411436685411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2074210099/10000000000 : ℝ)|^2127 ≤ (2519451630669/20000000000000 : ℝ)^1615
        have hw : |(-2074210099/10000000000 : ℝ)|=(2074210099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5174524197/10000000000 : ℝ)|^2127 ≤ (41991305144723/100000000000000 : ℝ)^1615
        have hw : |(5174524197/10000000000 : ℝ)|=(5174524197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2745747427/5000000000 : ℝ)|^2127 ≤ (45411436685411/100000000000000 : ℝ)^1615
        have hw : |(2745747427/5000000000 : ℝ)|=(2745747427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s2_5 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2643540059/5000000000 : ℝ)*x 0 + (-1921485329/10000000000 : ℝ)*x 1 + (5491494987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643540059/5000000000 : ℝ)^2127 ≤ (43198395562889/100000000000000 : ℝ)^1615 := by
    have hnat : (2643540059 : ℕ)^2127*100000000000000^1615 ≤ 43198395562889^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643540059 5000000000 43198395562889 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1921485329/10000000000 : ℝ)^2127 ≤ (11390166285127/100000000000000 : ℝ)^1615 := by
    have hnat : (1921485329 : ℕ)^2127*100000000000000^1615 ≤ 11390166285127^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1921485329 10000000000 11390166285127 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5491494987/10000000000 : ℝ)^2127 ≤ (283821488337/625000000000 : ℝ)^1615 := by
    have hnat : (5491494987 : ℕ)^2127*625000000000^1615 ≤ 283821488337^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5491494987 10000000000 283821488337 625000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643540059/5000000000 : ℝ), (-1921485329/10000000000 : ℝ), (5491494987/10000000000 : ℝ)] ![(43198395562889/100000000000000 : ℝ), (11390166285127/100000000000000 : ℝ), (283821488337/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643540059/5000000000 : ℝ)|^2127 ≤ (43198395562889/100000000000000 : ℝ)^1615
        have hw : |(2643540059/5000000000 : ℝ)|=(2643540059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1921485329/10000000000 : ℝ)|^2127 ≤ (11390166285127/100000000000000 : ℝ)^1615
        have hw : |(-1921485329/10000000000 : ℝ)|=(1921485329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5491494987/10000000000 : ℝ)|^2127 ≤ (283821488337/625000000000 : ℝ)^1615
        have hw : |(5491494987/10000000000 : ℝ)|=(5491494987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s2_6 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (132177007/250000000 : ℝ)*x 0 + (2745747431/5000000000 : ℝ)*x 1 + (-1921485281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132177007/250000000 : ℝ)^2127 ≤ (43198397306147/100000000000000 : ℝ)^1615 := by
    have hnat : (132177007 : ℕ)^2127*100000000000000^1615 ≤ 43198397306147^1615*250000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132177007 250000000 43198397306147 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2745747431/5000000000 : ℝ)^2127 ≤ (45411436772539/100000000000000 : ℝ)^1615 := by
    have hnat : (2745747431 : ℕ)^2127*100000000000000^1615 ≤ 45411436772539^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745747431 5000000000 45411436772539 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1921485281/10000000000 : ℝ)^2127 ≤ (2847541477597/25000000000000 : ℝ)^1615 := by
    have hnat : (1921485281 : ℕ)^2127*25000000000000^1615 ≤ 2847541477597^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1921485281 10000000000 2847541477597 25000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132177007/250000000 : ℝ), (2745747431/5000000000 : ℝ), (-1921485281/10000000000 : ℝ)] ![(43198397306147/100000000000000 : ℝ), (45411436772539/100000000000000 : ℝ), (2847541477597/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132177007/250000000 : ℝ)|^2127 ≤ (43198397306147/100000000000000 : ℝ)^1615
        have hw : |(132177007/250000000 : ℝ)|=(132177007/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2745747431/5000000000 : ℝ)|^2127 ≤ (45411436772539/100000000000000 : ℝ)^1615
        have hw : |(2745747431/5000000000 : ℝ)|=(2745747431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1921485281/10000000000 : ℝ)|^2127 ≤ (2847541477597/25000000000000 : ℝ)^1615
        have hw : |(-1921485281/10000000000 : ℝ)|=(1921485281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s2_7 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4331902671/10000000000 : ℝ)*x 0 + (4669725511/10000000000 : ℝ)*x 1 + (4017776839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4331902671/10000000000 : ℝ)^2127 ≤ (1038354700817/3125000000000 : ℝ)^1615 := by
    have hnat : (4331902671 : ℕ)^2127*3125000000000^1615 ≤ 1038354700817^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4331902671 10000000000 1038354700817 3125000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4669725511/10000000000 : ℝ)^2127 ≤ (36681534686181/100000000000000 : ℝ)^1615 := by
    have hnat : (4669725511 : ℕ)^2127*100000000000000^1615 ≤ 36681534686181^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4669725511 10000000000 36681534686181 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4017776839/10000000000 : ℝ)^2127 ≤ (30091114864743/100000000000000 : ℝ)^1615 := by
    have hnat : (4017776839 : ℕ)^2127*100000000000000^1615 ≤ 30091114864743^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4017776839 10000000000 30091114864743 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4331902671/10000000000 : ℝ), (4669725511/10000000000 : ℝ), (4017776839/10000000000 : ℝ)] ![(1038354700817/3125000000000 : ℝ), (36681534686181/100000000000000 : ℝ), (30091114864743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4331902671/10000000000 : ℝ)|^2127 ≤ (1038354700817/3125000000000 : ℝ)^1615
        have hw : |(4331902671/10000000000 : ℝ)|=(4331902671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4669725511/10000000000 : ℝ)|^2127 ≤ (36681534686181/100000000000000 : ℝ)^1615
        have hw : |(4669725511/10000000000 : ℝ)|=(4669725511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4017776839/10000000000 : ℝ)|^2127 ≤ (30091114864743/100000000000000 : ℝ)^1615
        have hw : |(4017776839/10000000000 : ℝ)|=(4017776839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1294_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152840397/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9917/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1607/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (9519/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4077/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9917/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1607/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9917/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1607/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9917/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1607/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9917/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1607/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9917/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1607/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9917/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1607/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1607/25000 : ℝ) ^ (4253/1024 : ℝ) ≤ (1120875281881087/100000000000000000000 : ℝ) := by
    have hpowers : (1607/25000 : ℝ)^4253 ≤ (1120875281881087/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1607 : ℕ)^4253*100000000000000000000^1024 ≤ 1120875281881087^1024*25000^4253 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1607 25000 1120875281881087 100000000000000000000 4253 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1607/25000 : ℝ)) (X := (1120875281881087/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9917/50000 : ℝ) ^ (4253/1024 : ℝ) ≤ (120759126960764329/100000000000000000000 : ℝ) := by
    have hpowers : (9917/50000 : ℝ)^4253 ≤ (120759126960764329/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9917 : ℕ)^4253*100000000000000000000^1024 ≤ 120759126960764329^1024*50000^4253 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9917 50000 120759126960764329 100000000000000000000 4253 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9917/50000 : ℝ)) (X := (120759126960764329/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001120875281881087/50000000000000000000 : ℝ) ≤ (1250006746805321/1250000000000000 : ℝ) ^ (4253/1024 : ℝ) := by
    have hpowers : (50001120875281881087/50000000000000000000 : ℝ)^1024 ≤ (1250006746805321/1250000000000000 : ℝ)^4253 := by
      have hnat : (50001120875281881087 : ℕ)^1024*1250000000000000^4253 ≤ 1250006746805321^4253*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001120875281881087 50000000000000000000 1250006746805321 1250000000000000 1024 4253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250006746805321/1250000000000000 : ℝ)) (X := (50001120875281881087/50000000000000000000 : ℝ)) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12515235000280330677/12500000000000000000 : ℝ) ≤ (1000293316293073/1000000000000000 : ℝ) ^ (4253/1024 : ℝ) := by
    have hpowers : (12515235000280330677/12500000000000000000 : ℝ)^1024 ≤ (1000293316293073/1000000000000000 : ℝ)^4253 := by
      have hnat : (12515235000280330677 : ℕ)^1024*1000000000000000^4253 ≤ 1000293316293073^4253*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12515235000280330677 12500000000000000000 1000293316293073 1000000000000000 1024 4253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000293316293073/1000000000000000 : ℝ)) (X := (12515235000280330677/12500000000000000000 : ℝ)) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50120759126960764329/50000000000000000000 : ℝ) ≤ (2501453087854723/2500000000000000 : ℝ) ^ (4253/1024 : ℝ) := by
    have hpowers : (50120759126960764329/50000000000000000000 : ℝ)^1024 ≤ (2501453087854723/2500000000000000 : ℝ)^4253 := by
      have hnat : (50120759126960764329 : ℕ)^1024*2500000000000000^4253 ≤ 2501453087854723^4253*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50120759126960764329 50000000000000000000 2501453087854723 2500000000000000 1024 4253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501453087854723/2500000000000000 : ℝ)) (X := (50120759126960764329/50000000000000000000 : ℝ)) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1120875281881087/100000000000000000000 : ℝ) ≤ ((523530112242864281/523671875000000000 : ℝ)+2*(1439594244081/670300000000000 : ℝ)*(1607/25000 : ℝ))^(4253/1024 : ℝ) := by
    rw [show (523530112242864281/523671875000000000 : ℝ)+2*(1439594244081/670300000000000 : ℝ)*(1607/25000 : ℝ)=(1250006746805321/1250000000000000 : ℝ) by norm_num, show 1+2*(1120875281881087/100000000000000000000 : ℝ)=(50001120875281881087/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(120759126960764329/100000000000000000000 : ℝ)+(1120875281881087/100000000000000000000 : ℝ) ≤ ((523530112242864281/523671875000000000 : ℝ)+(1439594244081/670300000000000 : ℝ)*((9917/50000 : ℝ)+(1607/25000 : ℝ)))^(4253/1024 : ℝ) := by
    rw [show (523530112242864281/523671875000000000 : ℝ)+(1439594244081/670300000000000 : ℝ)*((9917/50000 : ℝ)+(1607/25000 : ℝ))=(1000293316293073/1000000000000000 : ℝ) by norm_num, show 1+(120759126960764329/100000000000000000000 : ℝ)+(1120875281881087/100000000000000000000 : ℝ)=(12515235000280330677/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(120759126960764329/100000000000000000000 : ℝ) ≤ ((523530112242864281/523671875000000000 : ℝ)+2*(1439594244081/670300000000000 : ℝ)*(9917/50000 : ℝ))^(4253/1024 : ℝ) := by
    rw [show (523530112242864281/523671875000000000 : ℝ)+2*(1439594244081/670300000000000 : ℝ)*(9917/50000 : ℝ)=(2501453087854723/2500000000000000 : ℝ) by norm_num, show 1+2*(120759126960764329/100000000000000000000 : ℝ)=(50120759126960764329/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (523530112242864281/523671875000000000 : ℝ)*(X 1 0+X 2 0)+(1439594244081/670300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4253/1024 : ℝ)) (lo := (1607/25000 : ℝ)) (hi := (9917/50000 : ℝ)) (c := (523530112242864281/523671875000000000 : ℝ)) (alpha := (1439594244081/670300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (523530112242864281/523671875000000000 : ℝ)*(X 0 1+X 2 1)+(1439594244081/670300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4253/1024 : ℝ)) (lo := (1607/25000 : ℝ)) (hi := (9917/50000 : ℝ)) (c := (523530112242864281/523671875000000000 : ℝ)) (alpha := (1439594244081/670300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (523530112242864281/523671875000000000 : ℝ)*(X 0 2+X 1 2)+(1439594244081/670300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4253/1024 : ℝ)) (lo := (1607/25000 : ℝ)) (hi := (9917/50000 : ℝ)) (c := (523530112242864281/523671875000000000 : ℝ)) (alpha := (1439594244081/670300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-16593029/80000000 : ℝ)*X 0 0+(5493642237/10000000000 : ℝ)*X 0 1+(323274791/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2684717273/5000000000 : ℝ)*X 1 0+(-89623361/400000000 : ℝ)*X 1 1+(2586198381/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((536943453/1000000000 : ℝ)*X 2 0+(2586198331/5000000000 : ℝ)*X 2 1+(-1120292089/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((866347113/2000000000 : ℝ)*X 0 0+(4013355139/10000000000 : ℝ)*X 0 1+(2337051577/5000000000 : ℝ)*X 0 2+(866347113/2000000000 : ℝ)*X 1 0+(4013355139/10000000000 : ℝ)*X 1 1+(2337051577/5000000000 : ℝ)*X 1 2+(866347113/2000000000 : ℝ)*X 2 0+(4013355139/10000000000 : ℝ)*X 2 1+(2337051577/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2074210099/10000000000 : ℝ)*X 0 0+(5174524197/10000000000 : ℝ)*X 0 1+(2745747427/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2643540059/5000000000 : ℝ)*X 1 0+(-1921485329/10000000000 : ℝ)*X 1 1+(5491494987/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((132177007/250000000 : ℝ)*X 2 0+(2745747431/5000000000 : ℝ)*X 2 1+(-1921485281/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4331902671/10000000000 : ℝ)*X 0 0+(4669725511/10000000000 : ℝ)*X 0 1+(4017776839/10000000000 : ℝ)*X 0 2+(4331902671/10000000000 : ℝ)*X 1 0+(4669725511/10000000000 : ℝ)*X 1 1+(4017776839/10000000000 : ℝ)*X 1 2+(4331902671/10000000000 : ℝ)*X 2 0+(4669725511/10000000000 : ℝ)*X 2 1+(4017776839/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (328688188966245218215639053/52367187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1095354719/50000000000000 : ℝ)*(base19) + (1905808557/100000000000000 : ℝ)*(base23) + (29598999/20000000000000 : ℝ)*(lower2) + (302792791/50000000000000 : ℝ)*(upper3) + (1046933/390625000000 : ℝ)*(upper5) + (1156597460580899/50000000000000 : ℝ)*(major0) + (1156597460580899/50000000000000 : ℝ)*(major1) + (1156597460580899/50000000000000 : ℝ)*(major2) + (1556451770585093/50000000000000 : ℝ)*(sp0) + (778229137377743/25000000000000 : ℝ)*(sp1) + (1556458417205927/50000000000000 : ℝ)*(sp2) + (1513451734367801/100000000000000 : ℝ)*(sp3) + (607962009/4000000000000 : ℝ)*(sp4) + (1197407199/6250000000000 : ℝ)*(sp7) + (189183861610373/12500000000000 : ℝ)*(f.failure) + (311291874022041/10000000000000 : ℝ)*(f.sum) + (27855118051961/16757500000000000000000000000 : ℝ)*base66 + (188123111237715101/104734375000000000000000000000000 : ℝ)*base67 + (1162157395505691149/104734375000000000000000000000000 : ℝ)*base70 + (6529643816699593/3272949218750000000000000000000 : ℝ)*base71 + (92563020966193/33515000000000000000000000000 : ℝ)*base73 + (1118999763225909899/104734375000000000000000000000000 : ℝ)*base76 + (435984230807512631/26183593750000000000000000000000 : ℝ)*base78 + (296979469205540887/52367187500000000000000000000000 : ℝ)*base80 + (27268080109717/8378750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (6361919/1250000000000000000000 : ℝ)*base90 + (6361919/1250000000000000000000 : ℝ)*base92 + (6361919/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (221050402626878715151222779/52367187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (407681507/50000000000000 : ℝ)*(base19) + (544936403/50000000000000 : ℝ)*(base23) + (146520921/100000000000000 : ℝ)*(upper3) + (62847379/100000000000000 : ℝ)*(lower4) + (7488863/25000000000000 : ℝ)*(upper5) + (586090979387867/25000000000000 : ℝ)*(major0) + (586090979387867/25000000000000 : ℝ)*(major1) + (586090979387867/25000000000000 : ℝ)*(major2) + (4121702467/50000000000000 : ℝ)*(sp1) + (3007357381/25000000000000 : ℝ)*(sp2) + (3154863635177971/100000000000000 : ℝ)*(sp4) + (394356822051253/12500000000000 : ℝ)*(sp5) + (3154850515875641/100000000000000 : ℝ)*(sp6) + (306772811843909/20000000000000 : ℝ)*(sp7) + (306772811843909/20000000000000 : ℝ)*(f.failure) + (3154863635177971/100000000000000 : ℝ)*(f.sum) + (110897767383209/16757500000000000000000000000 : ℝ)*base65 + (58129594435754129/26183593750000000000000000000000 : ℝ)*base67 + (808934200477063391/104734375000000000000000000000000 : ℝ)*base69 + (495623621611344641/104734375000000000000000000000000 : ℝ)*base71 + (1240746909327/33515000000000000000000000000 : ℝ)*base74 + (511589493614905359/104734375000000000000000000000000 : ℝ)*base76 + (303145886954907141/104734375000000000000000000000000 : ℝ)*base77 + (615485784281625891/104734375000000000000000000000000 : ℝ)*base79 + (120645080690489/16757500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (6408127/2000000000000000000000 : ℝ)*base90 + (6408127/2000000000000000000000 : ℝ)*base92 + (6408127/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1294_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152840397/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9917/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1607/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9519/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4077/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1294_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1294_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152840397/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9519/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4077/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1294_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1294_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1294_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152840397/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9519/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4077/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1294_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

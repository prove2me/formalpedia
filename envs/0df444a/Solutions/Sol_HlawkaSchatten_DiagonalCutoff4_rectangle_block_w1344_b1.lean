-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1344_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:05:24.400158+00:00
-- url     : https://prove2.me/submissions/7e94e1e2-fd8e-4251-add1-3b511d88be44

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
theorem support_rectangle_w1344_s3_0 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-102025247/500000000 : ℝ)*x 0 + (2713456279/5000000000 : ℝ)*x 1 + (1307875871/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (102025247/500000000 : ℝ)^269 ≤ (12423418410571/100000000000000 : ℝ)^205 := by
    have hnat : (102025247 : ℕ)^269*100000000000000^205 ≤ 12423418410571^205*500000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102025247 500000000 12423418410571 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713456279/5000000000 : ℝ)^269 ≤ (44841642352261/100000000000000 : ℝ)^205 := by
    have hnat : (2713456279 : ℕ)^269*100000000000000^205 ≤ 44841642352261^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713456279 5000000000 44841642352261 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1307875871/2500000000 : ℝ)^269 ≤ (42734939221053/100000000000000 : ℝ)^205 := by
    have hnat : (1307875871 : ℕ)^269*100000000000000^205 ≤ 42734939221053^205*2500000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307875871 2500000000 42734939221053 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-102025247/500000000 : ℝ), (2713456279/5000000000 : ℝ), (1307875871/2500000000 : ℝ)] ![(12423418410571/100000000000000 : ℝ), (44841642352261/100000000000000 : ℝ), (42734939221053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-102025247/500000000 : ℝ)|^269 ≤ (12423418410571/100000000000000 : ℝ)^205
        have hw : |(-102025247/500000000 : ℝ)|=(102025247/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713456279/5000000000 : ℝ)|^269 ≤ (44841642352261/100000000000000 : ℝ)^205
        have hw : |(2713456279/5000000000 : ℝ)|=(2713456279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1307875871/2500000000 : ℝ)|^269 ≤ (42734939221053/100000000000000 : ℝ)^205
        have hw : |(1307875871/2500000000 : ℝ)|=(1307875871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s3_1 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2676306851/5000000000 : ℝ)*x 0 + (-133773029/625000000 : ℝ)*x 1 + (653937923/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676306851/5000000000 : ℝ)^269 ≤ (44037788364309/100000000000000 : ℝ)^205 := by
    have hnat : (2676306851 : ℕ)^269*100000000000000^205 ≤ 44037788364309^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676306851 5000000000 44037788364309 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (133773029/625000000 : ℝ)^269 ≤ (3306818368497/25000000000000 : ℝ)^205 := by
    have hnat : (133773029 : ℕ)^269*25000000000000^205 ≤ 3306818368497^205*625000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133773029 625000000 3306818368497 25000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (653937923/1250000000 : ℝ)^269 ≤ (1335466817161/3125000000000 : ℝ)^205 := by
    have hnat : (653937923 : ℕ)^269*3125000000000^205 ≤ 1335466817161^205*1250000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653937923 1250000000 1335466817161 3125000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676306851/5000000000 : ℝ), (-133773029/625000000 : ℝ), (653937923/1250000000 : ℝ)] ![(44037788364309/100000000000000 : ℝ), (3306818368497/25000000000000 : ℝ), (1335466817161/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676306851/5000000000 : ℝ)|^269 ≤ (44037788364309/100000000000000 : ℝ)^205
        have hw : |(2676306851/5000000000 : ℝ)|=(2676306851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-133773029/625000000 : ℝ)|^269 ≤ (3306818368497/25000000000000 : ℝ)^205
        have hw : |(-133773029/625000000 : ℝ)|=(133773029/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(653937923/1250000000 : ℝ)|^269 ≤ (1335466817161/3125000000000 : ℝ)^205
        have hw : |(653937923/1250000000 : ℝ)|=(653937923/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s3_2 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5352613847/10000000000 : ℝ)*x 0 + (5231503169/10000000000 : ℝ)*x 1 + (-535092139/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352613847/10000000000 : ℝ)^269 ≤ (44037789929711/100000000000000 : ℝ)^205 := by
    have hnat : (5352613847 : ℕ)^269*100000000000000^205 ≤ 44037789929711^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352613847 10000000000 44037789929711 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5231503169/10000000000 : ℝ)^269 ≤ (42734935844563/100000000000000 : ℝ)^205 := by
    have hnat : (5231503169 : ℕ)^269*100000000000000^205 ≤ 42734935844563^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231503169 10000000000 42734935844563 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (535092139/2500000000 : ℝ)^269 ≤ (13227274220039/100000000000000 : ℝ)^205 := by
    have hnat : (535092139 : ℕ)^269*100000000000000^205 ≤ 13227274220039^205*2500000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535092139 2500000000 13227274220039 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352613847/10000000000 : ℝ), (5231503169/10000000000 : ℝ), (-535092139/2500000000 : ℝ)] ![(44037789929711/100000000000000 : ℝ), (42734935844563/100000000000000 : ℝ), (13227274220039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352613847/10000000000 : ℝ)|^269 ≤ (44037789929711/100000000000000 : ℝ)^205
        have hw : |(5352613847/10000000000 : ℝ)|=(5352613847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5231503169/10000000000 : ℝ)|^269 ≤ (42734935844563/100000000000000 : ℝ)^205
        have hw : |(5231503169/10000000000 : ℝ)|=(5231503169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-535092139/2500000000 : ℝ)|^269 ≤ (13227274220039/100000000000000 : ℝ)^205
        have hw : |(-535092139/2500000000 : ℝ)|=(535092139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s3_3 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (33789409/78125000 : ℝ)*x 0 + (1031191549/2500000000 : ℝ)*x 1 + (4534372811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33789409/78125000 : ℝ)^269 ≤ (16646333831623/50000000000000 : ℝ)^205 := by
    have hnat : (33789409 : ℕ)^269*50000000000000^205 ≤ 16646333831623^205*78125000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33789409 78125000 16646333831623 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1031191549/2500000000 : ℝ)^269 ≤ (31284476020401/100000000000000 : ℝ)^205 := by
    have hnat : (1031191549 : ℕ)^269*100000000000000^205 ≤ 31284476020401^205*2500000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031191549 2500000000 31284476020401 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4534372811/10000000000 : ℝ)^269 ≤ (17711428155281/50000000000000 : ℝ)^205 := by
    have hnat : (4534372811 : ℕ)^269*50000000000000^205 ≤ 17711428155281^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4534372811 10000000000 17711428155281 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33789409/78125000 : ℝ), (1031191549/2500000000 : ℝ), (4534372811/10000000000 : ℝ)] ![(16646333831623/50000000000000 : ℝ), (31284476020401/100000000000000 : ℝ), (17711428155281/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33789409/78125000 : ℝ)|^269 ≤ (16646333831623/50000000000000 : ℝ)^205
        have hw : |(33789409/78125000 : ℝ)|=(33789409/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1031191549/2500000000 : ℝ)|^269 ≤ (31284476020401/100000000000000 : ℝ)^205
        have hw : |(1031191549/2500000000 : ℝ)|=(1031191549/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4534372811/10000000000 : ℝ)|^269 ≤ (17711428155281/50000000000000 : ℝ)^205
        have hw : |(4534372811/10000000000 : ℝ)|=(4534372811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s3_4 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-204052423/1000000000 : ℝ)*x 0 + (163509899/312500000 : ℝ)*x 1 + (135652357/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (204052423/1000000000 : ℝ)^269 ≤ (2484714504393/20000000000000 : ℝ)^205 := by
    have hnat : (204052423 : ℕ)^269*20000000000000^205 ≤ 2484714504393^205*1000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204052423 1000000000 2484714504393 20000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163509899/312500000 : ℝ)^269 ≤ (21371828519119/50000000000000 : ℝ)^205 := by
    have hnat : (163509899 : ℕ)^269*50000000000000^205 ≤ 21371828519119^205*312500000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163509899 312500000 21371828519119 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135652357/250000000 : ℝ)^269 ≤ (22416385214689/50000000000000 : ℝ)^205 := by
    have hnat : (135652357 : ℕ)^269*50000000000000^205 ≤ 22416385214689^205*250000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135652357 250000000 22416385214689 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-204052423/1000000000 : ℝ), (163509899/312500000 : ℝ), (135652357/250000000 : ℝ)] ![(2484714504393/20000000000000 : ℝ), (21371828519119/50000000000000 : ℝ), (22416385214689/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-204052423/1000000000 : ℝ)|^269 ≤ (2484714504393/20000000000000 : ℝ)^205
        have hw : |(-204052423/1000000000 : ℝ)|=(204052423/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163509899/312500000 : ℝ)|^269 ≤ (21371828519119/50000000000000 : ℝ)^205
        have hw : |(163509899/312500000 : ℝ)|=(163509899/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135652357/250000000 : ℝ)|^269 ≤ (22416385214689/50000000000000 : ℝ)^205
        have hw : |(135652357/250000000 : ℝ)|=(135652357/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s3_5 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2651133771/5000000000 : ℝ)*x 0 + (-972888817/5000000000 : ℝ)*x 1 + (1085218917/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651133771/5000000000 : ℝ)^269 ≤ (4349505706239/10000000000000 : ℝ)^205 := by
    have hnat : (2651133771 : ℕ)^269*10000000000000^205 ≤ 4349505706239^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651133771 5000000000 4349505706239 10000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (972888817/5000000000 : ℝ)^269 ≤ (11672169190047/100000000000000 : ℝ)^205 := by
    have hnat : (972888817 : ℕ)^269*100000000000000^205 ≤ 11672169190047^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      972888817 5000000000 11672169190047 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085218917/2000000000 : ℝ)^269 ≤ (44832773736167/100000000000000 : ℝ)^205 := by
    have hnat : (1085218917 : ℕ)^269*100000000000000^205 ≤ 44832773736167^205*2000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085218917 2000000000 44832773736167 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651133771/5000000000 : ℝ), (-972888817/5000000000 : ℝ), (1085218917/2000000000 : ℝ)] ![(4349505706239/10000000000000 : ℝ), (11672169190047/100000000000000 : ℝ), (44832773736167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651133771/5000000000 : ℝ)|^269 ≤ (4349505706239/10000000000000 : ℝ)^205
        have hw : |(2651133771/5000000000 : ℝ)|=(2651133771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-972888817/5000000000 : ℝ)|^269 ≤ (11672169190047/100000000000000 : ℝ)^205
        have hw : |(-972888817/5000000000 : ℝ)|=(972888817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1085218917/2000000000 : ℝ)|^269 ≤ (44832773736167/100000000000000 : ℝ)^205
        have hw : |(1085218917/2000000000 : ℝ)|=(1085218917/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s3_6 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5302268383/10000000000 : ℝ)*x 0 + (2713047019/5000000000 : ℝ)*x 1 + (-1945777237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302268383/10000000000 : ℝ)^269 ≤ (1359220816093/3125000000000 : ℝ)^205 := by
    have hnat : (5302268383 : ℕ)^269*3125000000000^205 ≤ 1359220816093^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302268383 10000000000 1359220816093 3125000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713047019/5000000000 : ℝ)^269 ≤ (4483276780563/10000000000000 : ℝ)^205 := by
    have hnat : (2713047019 : ℕ)^269*10000000000000^205 ≤ 4483276780563^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713047019 5000000000 4483276780563 10000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1945777237/10000000000 : ℝ)^269 ≤ (5836083032533/50000000000000 : ℝ)^205 := by
    have hnat : (1945777237 : ℕ)^269*50000000000000^205 ≤ 5836083032533^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1945777237 10000000000 5836083032533 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302268383/10000000000 : ℝ), (2713047019/5000000000 : ℝ), (-1945777237/10000000000 : ℝ)] ![(1359220816093/3125000000000 : ℝ), (4483276780563/10000000000000 : ℝ), (5836083032533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302268383/10000000000 : ℝ)|^269 ≤ (1359220816093/3125000000000 : ℝ)^205
        have hw : |(5302268383/10000000000 : ℝ)|=(5302268383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713047019/5000000000 : ℝ)|^269 ≤ (4483276780563/10000000000000 : ℝ)^205
        have hw : |(2713047019/5000000000 : ℝ)|=(2713047019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1945777237/10000000000 : ℝ)|^269 ≤ (5836083032533/50000000000000 : ℝ)^205
        have hw : |(-1945777237/10000000000 : ℝ)|=(1945777237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s3_7 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (432508513/1000000000 : ℝ)*x 0 + (4532667651/10000000000 : ℝ)*x 1 + (1031620227/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (432508513/1000000000 : ℝ)^269 ≤ (33293079554917/100000000000000 : ℝ)^205 := by
    have hnat : (432508513 : ℕ)^269*100000000000000^205 ≤ 33293079554917^205*1000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432508513 1000000000 33293079554917 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4532667651/10000000000 : ℝ)^269 ≤ (35405377800379/100000000000000 : ℝ)^205 := by
    have hnat : (4532667651 : ℕ)^269*100000000000000^205 ≤ 35405377800379^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4532667651 10000000000 35405377800379 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1031620227/2500000000 : ℝ)^269 ≤ (15650771316561/50000000000000 : ℝ)^205 := by
    have hnat : (1031620227 : ℕ)^269*50000000000000^205 ≤ 15650771316561^205*2500000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031620227 2500000000 15650771316561 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(432508513/1000000000 : ℝ), (4532667651/10000000000 : ℝ), (1031620227/2500000000 : ℝ)] ![(33293079554917/100000000000000 : ℝ), (35405377800379/100000000000000 : ℝ), (15650771316561/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(432508513/1000000000 : ℝ)|^269 ≤ (33293079554917/100000000000000 : ℝ)^205
        have hw : |(432508513/1000000000 : ℝ)|=(432508513/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4532667651/10000000000 : ℝ)|^269 ≤ (35405377800379/100000000000000 : ℝ)^205
        have hw : |(4532667651/10000000000 : ℝ)|=(4532667651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1031620227/2500000000 : ℝ)|^269 ≤ (15650771316561/50000000000000 : ℝ)^205
        have hw : |(1031620227/2500000000 : ℝ)|=(1031620227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1344_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154807433/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (503/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1973/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (1359/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (469/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (503/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1973/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (503/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1973/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (503/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1973/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (503/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1973/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (503/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1973/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (503/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1973/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1973/20000 : ℝ) ^ (4303/1024 : ℝ) ≤ (1482472566562379/25000000000000000000 : ℝ) := by
    have hpowers : (1973/20000 : ℝ)^4303 ≤ (1482472566562379/25000000000000000000 : ℝ)^1024 := by
      have hnat : (1973 : ℕ)^4303*25000000000000000000^1024 ≤ 1482472566562379^1024*20000^4303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1973 20000 1482472566562379 25000000000000000000 4303 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1973/20000 : ℝ)) (X := (1482472566562379/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (503/3125 : ℝ) ^ (4303/1024 : ℝ) ≤ (1449977125574079/3125000000000000000 : ℝ) := by
    have hpowers : (503/3125 : ℝ)^4303 ≤ (1449977125574079/3125000000000000000 : ℝ)^1024 := by
      have hnat : (503 : ℕ)^4303*3125000000000000000^1024 ≤ 1449977125574079^1024*3125^4303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        503 3125 1449977125574079 3125000000000000000 4303 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (503/3125 : ℝ)) (X := (1449977125574079/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501482472566562379/12500000000000000000 : ℝ) ≤ (1250035277325499/1250000000000000 : ℝ) ^ (4303/1024 : ℝ) := by
    have hpowers : (12501482472566562379/12500000000000000000 : ℝ)^1024 ≤ (1250035277325499/1250000000000000 : ℝ)^4303 := by
      have hnat : (12501482472566562379 : ℕ)^1024*1250000000000000^4303 ≤ 1250035277325499^4303*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501482472566562379 12500000000000000000 1250035277325499 1250000000000000 1024 4303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250035277325499/1250000000000000 : ℝ)) (X := (12501482472566562379/12500000000000000000 : ℝ)) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25013082289571155011/25000000000000000000 : ℝ) ≤ (2000249009423761/2000000000000000 : ℝ) ^ (4303/1024 : ℝ) := by
    have hpowers : (25013082289571155011/25000000000000000000 : ℝ)^1024 ≤ (2000249009423761/2000000000000000 : ℝ)^4303 := by
      have hnat : (25013082289571155011 : ℕ)^1024*2000000000000000^4303 ≤ 2000249009423761^4303*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013082289571155011 25000000000000000000 2000249009423761 2000000000000000 1024 4303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000249009423761/2000000000000000 : ℝ)) (X := (25013082289571155011/25000000000000000000 : ℝ)) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1563949977125574079/1562500000000000000 : ℝ) ≤ (5001103937816809/5000000000000000 : ℝ) ^ (4303/1024 : ℝ) := by
    have hpowers : (1563949977125574079/1562500000000000000 : ℝ)^1024 ≤ (5001103937816809/5000000000000000 : ℝ)^4303 := by
      have hnat : (1563949977125574079 : ℕ)^1024*5000000000000000^4303 ≤ 5001103937816809^4303*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563949977125574079 1562500000000000000 5001103937816809 5000000000000000 1024 4303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001103937816809/5000000000000000 : ℝ)) (X := (1563949977125574079/1562500000000000000 : ℝ)) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1482472566562379/25000000000000000000 : ℝ) ≤ ((10382126982920702277/10385000000000000000 : ℝ)+2*(320942838271/207700000000000 : ℝ)*(1973/20000 : ℝ))^(4303/1024 : ℝ) := by
    rw [show (10382126982920702277/10385000000000000000 : ℝ)+2*(320942838271/207700000000000 : ℝ)*(1973/20000 : ℝ)=(1250035277325499/1250000000000000 : ℝ) by norm_num, show 1+2*(1482472566562379/25000000000000000000 : ℝ)=(12501482472566562379/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1449977125574079/3125000000000000000 : ℝ)+(1482472566562379/25000000000000000000 : ℝ) ≤ ((10382126982920702277/10385000000000000000 : ℝ)+(320942838271/207700000000000 : ℝ)*((503/3125 : ℝ)+(1973/20000 : ℝ)))^(4303/1024 : ℝ) := by
    rw [show (10382126982920702277/10385000000000000000 : ℝ)+(320942838271/207700000000000 : ℝ)*((503/3125 : ℝ)+(1973/20000 : ℝ))=(2000249009423761/2000000000000000 : ℝ) by norm_num, show 1+(1449977125574079/3125000000000000000 : ℝ)+(1482472566562379/25000000000000000000 : ℝ)=(25013082289571155011/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1449977125574079/3125000000000000000 : ℝ) ≤ ((10382126982920702277/10385000000000000000 : ℝ)+2*(320942838271/207700000000000 : ℝ)*(503/3125 : ℝ))^(4303/1024 : ℝ) := by
    rw [show (10382126982920702277/10385000000000000000 : ℝ)+2*(320942838271/207700000000000 : ℝ)*(503/3125 : ℝ)=(5001103937816809/5000000000000000 : ℝ) by norm_num, show 1+2*(1449977125574079/3125000000000000000 : ℝ)=(1563949977125574079/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10382126982920702277/10385000000000000000 : ℝ)*(X 1 0+X 2 0)+(320942838271/207700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4303/1024 : ℝ)) (lo := (1973/20000 : ℝ)) (hi := (503/3125 : ℝ)) (c := (10382126982920702277/10385000000000000000 : ℝ)) (alpha := (320942838271/207700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10382126982920702277/10385000000000000000 : ℝ)*(X 0 1+X 2 1)+(320942838271/207700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4303/1024 : ℝ)) (lo := (1973/20000 : ℝ)) (hi := (503/3125 : ℝ)) (c := (10382126982920702277/10385000000000000000 : ℝ)) (alpha := (320942838271/207700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10382126982920702277/10385000000000000000 : ℝ)*(X 0 2+X 1 2)+(320942838271/207700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4303/1024 : ℝ)) (lo := (1973/20000 : ℝ)) (hi := (503/3125 : ℝ)) (c := (10382126982920702277/10385000000000000000 : ℝ)) (alpha := (320942838271/207700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-102025247/500000000 : ℝ)*X 0 0+(2713456279/5000000000 : ℝ)*X 0 1+(1307875871/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676306851/5000000000 : ℝ)*X 1 0+(-133773029/625000000 : ℝ)*X 1 1+(653937923/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352613847/10000000000 : ℝ)*X 2 0+(5231503169/10000000000 : ℝ)*X 2 1+(-535092139/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((33789409/78125000 : ℝ)*X 0 0+(1031191549/2500000000 : ℝ)*X 0 1+(4534372811/10000000000 : ℝ)*X 0 2+(33789409/78125000 : ℝ)*X 1 0+(1031191549/2500000000 : ℝ)*X 1 1+(4534372811/10000000000 : ℝ)*X 1 2+(33789409/78125000 : ℝ)*X 2 0+(1031191549/2500000000 : ℝ)*X 2 1+(4534372811/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-204052423/1000000000 : ℝ)*X 0 0+(163509899/312500000 : ℝ)*X 0 1+(135652357/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2651133771/5000000000 : ℝ)*X 1 0+(-972888817/5000000000 : ℝ)*X 1 1+(1085218917/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5302268383/10000000000 : ℝ)*X 2 0+(2713047019/5000000000 : ℝ)*X 2 1+(-1945777237/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((432508513/1000000000 : ℝ)*X 0 0+(4532667651/10000000000 : ℝ)*X 0 1+(1031620227/2500000000 : ℝ)*X 0 2+(432508513/1000000000 : ℝ)*X 1 0+(4532667651/10000000000 : ℝ)*X 1 1+(1031620227/2500000000 : ℝ)*X 1 2+(432508513/1000000000 : ℝ)*X 2 0+(4532667651/10000000000 : ℝ)*X 2 1+(1031620227/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (47758100135762716679679/5192500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1857572867/100000000000000 : ℝ)*(base19) + (35287799/2000000000000 : ℝ)*(base23) + (124081351/100000000000000 : ℝ)*(lower2) + (308863767/100000000000000 : ℝ)*(upper3) + (59476063/100000000000000 : ℝ)*(upper5) + (1889731106455813/50000000000000 : ℝ)*(major0) + (1889731106455813/50000000000000 : ℝ)*(major1) + (1889731106455813/50000000000000 : ℝ)*(major2) + (1279375317970901/25000000000000 : ℝ)*(sp0) + (5117526432235241/100000000000000 : ℝ)*(sp1) + (2558763262709079/50000000000000 : ℝ)*(sp2) + (2441379029604281/100000000000000 : ℝ)*(sp3) + (5403584901/20000000000000 : ℝ)*(sp4) + (16799827001/100000000000000 : ℝ)*(sp7) + (1220697914715641/50000000000000 : ℝ)*(f.failure) + (5117528289808109/100000000000000 : ℝ)*(f.sum) + (93384521087/5192500000000000000000000000 : ℝ)*base66 + (1214769828364386201/519250000000000000000000000000000 : ℝ)*base67 + (4038212378403613799/519250000000000000000000000000000 : ℝ)*base70 + (3308421919416863799/519250000000000000000000000000000 : ℝ)*base72 + (26944211995991/10385000000000000000000000000 : ℝ)*base73 + (970084822292386201/519250000000000000000000000000000 : ℝ)*base75 + (458861853063863799/519250000000000000000000000000000 : ℝ)*base78 + (3449806769636886201/519250000000000000000000000000000 : ℝ)*base79 + (20426664837489/10385000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (8159553/5000000000000000000000 : ℝ)*base89 + (8159553/5000000000000000000000 : ℝ)*base91 + (8159553/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (634757062086045239630678961/64906250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1835832219/100000000000000 : ℝ)*(base19) + (3269348773/100000000000000 : ℝ)*(base23) + (43504823/12500000000000 : ℝ)*(upper3) + (1704463/800000000000 : ℝ)*(lower4) + (30325833/10000000000000 : ℝ)*(upper5) + (952810361464981/25000000000000 : ℝ)*(major0) + (952810361464981/25000000000000 : ℝ)*(major1) + (952810361464981/25000000000000 : ℝ)*(major2) + (33354578279/100000000000000 : ℝ)*(sp1) + (55805574107/100000000000000 : ℝ)*(sp2) + (5160558501751149/100000000000000 : ℝ)*(sp4) + (103210466226813/2000000000000 : ℝ)*(sp5) + (516049942682827/10000000000000 : ℝ)*(sp6) + (2461924063982073/100000000000000 : ℝ)*(sp7) + (2461924063982073/100000000000000 : ℝ)*(f.failure) + (5160558501751149/100000000000000 : ℝ)*(f.sum) + (398628234011/162265625000000000000000000 : ℝ)*base65 + (1022949390736863263/259625000000000000000000000000000 : ℝ)*base68 + (4652507682333488263/259625000000000000000000000000000 : ℝ)*base70 + (2613269007656988263/259625000000000000000000000000000 : ℝ)*base72 + (53957025769109/10385000000000000000000000000 : ℝ)*base73 + (808847332756261737/259625000000000000000000000000000 : ℝ)*base75 + (3469326854511613263/259625000000000000000000000000000 : ℝ)*base78 + (5554894047755238263/259625000000000000000000000000000 : ℝ)*base80 + (18970375698683/5192500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (79148609/10000000000000000000000 : ℝ)*base89 + (79148609/10000000000000000000000 : ℝ)*base91 + (79148609/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1344_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154807433/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (503/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1973/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1359/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (469/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1344_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1344_s4_0 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2041948811/10000000000 : ℝ)*x 0 + (1083026271/2000000000 : ℝ)*x 1 + (5242336527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2041948811/10000000000 : ℝ)^269 ≤ (12434955021173/100000000000000 : ℝ)^205 := by
    have hnat : (2041948811 : ℕ)^269*100000000000000^205 ≤ 12434955021173^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2041948811 10000000000 12434955021173 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083026271/2000000000 : ℝ)^269 ≤ (44713948650467/100000000000000 : ℝ)^205 := by
    have hnat : (1083026271 : ℕ)^269*100000000000000^205 ≤ 44713948650467^205*2000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083026271 2000000000 44713948650467 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242336527/10000000000 : ℝ)^269 ≤ (21425548158837/50000000000000 : ℝ)^205 := by
    have hnat : (5242336527 : ℕ)^269*50000000000000^205 ≤ 21425548158837^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242336527 10000000000 21425548158837 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2041948811/10000000000 : ℝ), (1083026271/2000000000 : ℝ), (5242336527/10000000000 : ℝ)] ![(12434955021173/100000000000000 : ℝ), (44713948650467/100000000000000 : ℝ), (21425548158837/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2041948811/10000000000 : ℝ)|^269 ≤ (12434955021173/100000000000000 : ℝ)^205
        have hw : |(-2041948811/10000000000 : ℝ)|=(2041948811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083026271/2000000000 : ℝ)|^269 ≤ (44713948650467/100000000000000 : ℝ)^205
        have hw : |(1083026271/2000000000 : ℝ)|=(1083026271/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242336527/10000000000 : ℝ)|^269 ≤ (21425548158837/50000000000000 : ℝ)^205
        have hw : |(5242336527/10000000000 : ℝ)|=(5242336527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s4_1 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2674805023/5000000000 : ℝ)*x 0 + (-2130034961/10000000000 : ℝ)*x 1 + (5242336503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674805023/5000000000 : ℝ)^269 ≤ (1100134102443/2500000000000 : ℝ)^205 := by
    have hnat : (2674805023 : ℕ)^269*2500000000000^205 ≤ 1100134102443^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674805023 5000000000 1100134102443 2500000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2130034961/10000000000 : ℝ)^269 ≤ (13143539829097/100000000000000 : ℝ)^205 := by
    have hnat : (2130034961 : ℕ)^269*100000000000000^205 ≤ 13143539829097^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130034961 10000000000 13143539829097 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242336503/10000000000 : ℝ)^269 ≤ (42851096060251/100000000000000 : ℝ)^205 := by
    have hnat : (5242336503 : ℕ)^269*100000000000000^205 ≤ 42851096060251^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242336503 10000000000 42851096060251 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674805023/5000000000 : ℝ), (-2130034961/10000000000 : ℝ), (5242336503/10000000000 : ℝ)] ![(1100134102443/2500000000000 : ℝ), (13143539829097/100000000000000 : ℝ), (42851096060251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674805023/5000000000 : ℝ)|^269 ≤ (1100134102443/2500000000000 : ℝ)^205
        have hw : |(2674805023/5000000000 : ℝ)|=(2674805023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2130034961/10000000000 : ℝ)|^269 ≤ (13143539829097/100000000000000 : ℝ)^205
        have hw : |(-2130034961/10000000000 : ℝ)|=(2130034961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242336503/10000000000 : ℝ)|^269 ≤ (42851096060251/100000000000000 : ℝ)^205
        have hw : |(5242336503/10000000000 : ℝ)|=(5242336503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s4_2 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5349610147/10000000000 : ℝ)*x 0 + (5242336361/10000000000 : ℝ)*x 1 + (-1065017507/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349610147/10000000000 : ℝ)^269 ≤ (5500670648489/12500000000000 : ℝ)^205 := by
    have hnat : (5349610147 : ℕ)^269*12500000000000^205 ≤ 5500670648489^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349610147 10000000000 5500670648489 12500000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242336361/10000000000 : ℝ)^269 ≤ (2678193408573/6250000000000 : ℝ)^205 := by
    have hnat : (5242336361 : ℕ)^269*6250000000000^205 ≤ 2678193408573^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242336361 10000000000 2678193408573 6250000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1065017507/5000000000 : ℝ)^269 ≤ (6571770129119/50000000000000 : ℝ)^205 := by
    have hnat : (1065017507 : ℕ)^269*50000000000000^205 ≤ 6571770129119^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065017507 5000000000 6571770129119 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349610147/10000000000 : ℝ), (5242336361/10000000000 : ℝ), (-1065017507/5000000000 : ℝ)] ![(5500670648489/12500000000000 : ℝ), (2678193408573/6250000000000 : ℝ), (6571770129119/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349610147/10000000000 : ℝ)|^269 ≤ (5500670648489/12500000000000 : ℝ)^205
        have hw : |(5349610147/10000000000 : ℝ)|=(5349610147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242336361/10000000000 : ℝ)|^269 ≤ (2678193408573/6250000000000 : ℝ)^205
        have hw : |(5242336361/10000000000 : ℝ)|=(5242336361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1065017507/5000000000 : ℝ)|^269 ≤ (6571770129119/50000000000000 : ℝ)^205
        have hw : |(-1065017507/5000000000 : ℝ)|=(1065017507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s4_3 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2162960719/5000000000 : ℝ)*x 0 + (4148359001/10000000000 : ℝ)*x 1 + (4510562921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2162960719/5000000000 : ℝ)^269 ≤ (33301527227759/100000000000000 : ℝ)^205 := by
    have hnat : (2162960719 : ℕ)^269*100000000000000^205 ≤ 33301527227759^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162960719 5000000000 33301527227759 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4148359001/10000000000 : ℝ)^269 ≤ (31519490501909/100000000000000 : ℝ)^205 := by
    have hnat : (4148359001 : ℕ)^269*100000000000000^205 ≤ 31519490501909^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4148359001 10000000000 31519490501909 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4510562921/10000000000 : ℝ)^269 ≤ (35178982250123/100000000000000 : ℝ)^205 := by
    have hnat : (4510562921 : ℕ)^269*100000000000000^205 ≤ 35178982250123^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4510562921 10000000000 35178982250123 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2162960719/5000000000 : ℝ), (4148359001/10000000000 : ℝ), (4510562921/10000000000 : ℝ)] ![(33301527227759/100000000000000 : ℝ), (31519490501909/100000000000000 : ℝ), (35178982250123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2162960719/5000000000 : ℝ)|^269 ≤ (33301527227759/100000000000000 : ℝ)^205
        have hw : |(2162960719/5000000000 : ℝ)|=(2162960719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4148359001/10000000000 : ℝ)|^269 ≤ (31519490501909/100000000000000 : ℝ)^205
        have hw : |(4148359001/10000000000 : ℝ)|=(4148359001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4510562921/10000000000 : ℝ)|^269 ≤ (35178982250123/100000000000000 : ℝ)^205
        have hw : |(4510562921/10000000000 : ℝ)|=(4510562921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s4_4 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1020981069/5000000000 : ℝ)*x 0 + (2621486409/5000000000 : ℝ)*x 1 + (270724581/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1020981069/5000000000 : ℝ)^269 ≤ (12435061516519/100000000000000 : ℝ)^205 := by
    have hnat : (1020981069 : ℕ)^269*100000000000000^205 ≤ 12435061516519^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020981069 5000000000 12435061516519 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621486409/5000000000 : ℝ)^269 ≤ (42857921267583/100000000000000 : ℝ)^205 := by
    have hnat : (2621486409 : ℕ)^269*100000000000000^205 ≤ 42857921267583^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621486409 5000000000 42857921267583 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270724581/500000000 : ℝ)^269 ≤ (11176754298303/25000000000000 : ℝ)^205 := by
    have hnat : (270724581 : ℕ)^269*25000000000000^205 ≤ 11176754298303^205*500000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270724581 500000000 11176754298303 25000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1020981069/5000000000 : ℝ), (2621486409/5000000000 : ℝ), (270724581/500000000 : ℝ)] ![(12435061516519/100000000000000 : ℝ), (42857921267583/100000000000000 : ℝ), (11176754298303/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1020981069/5000000000 : ℝ)|^269 ≤ (12435061516519/100000000000000 : ℝ)^205
        have hw : |(-1020981069/5000000000 : ℝ)|=(1020981069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621486409/5000000000 : ℝ)|^269 ≤ (42857921267583/100000000000000 : ℝ)^205
        have hw : |(2621486409/5000000000 : ℝ)|=(2621486409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270724581/500000000 : ℝ)|^269 ≤ (11176754298303/25000000000000 : ℝ)^205
        have hw : |(270724581/500000000 : ℝ)|=(270724581/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s4_5 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5305091931/10000000000 : ℝ)*x 0 + (-1957879829/10000000000 : ℝ)*x 1 + (1082898277/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305091931/10000000000 : ℝ)^269 ≤ (43525461522991/100000000000000 : ℝ)^205 := by
    have hnat : (5305091931 : ℕ)^269*100000000000000^205 ≤ 43525461522991^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305091931 10000000000 43525461522991 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1957879829/10000000000 : ℝ)^269 ≤ (2941880954609/25000000000000 : ℝ)^205 := by
    have hnat : (1957879829 : ℕ)^269*25000000000000^205 ≤ 2941880954609^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1957879829 10000000000 2941880954609 25000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082898277/2000000000 : ℝ)^269 ≤ (2235350732353/5000000000000 : ℝ)^205 := by
    have hnat : (1082898277 : ℕ)^269*5000000000000^205 ≤ 2235350732353^205*2000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082898277 2000000000 2235350732353 5000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305091931/10000000000 : ℝ), (-1957879829/10000000000 : ℝ), (1082898277/2000000000 : ℝ)] ![(43525461522991/100000000000000 : ℝ), (2941880954609/25000000000000 : ℝ), (2235350732353/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305091931/10000000000 : ℝ)|^269 ≤ (43525461522991/100000000000000 : ℝ)^205
        have hw : |(5305091931/10000000000 : ℝ)|=(5305091931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1957879829/10000000000 : ℝ)|^269 ≤ (2941880954609/25000000000000 : ℝ)^205
        have hw : |(-1957879829/10000000000 : ℝ)|=(1957879829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082898277/2000000000 : ℝ)|^269 ≤ (2235350732353/5000000000000 : ℝ)^205
        have hw : |(1082898277/2000000000 : ℝ)|=(1082898277/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s4_6 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (663136467/1250000000 : ℝ)*x 0 + (2707245743/5000000000 : ℝ)*x 1 + (-489469989/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663136467/1250000000 : ℝ)^269 ≤ (1360170606989/3125000000000 : ℝ)^205 := by
    have hnat : (663136467 : ℕ)^269*3125000000000^205 ≤ 1360170606989^205*1250000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663136467 1250000000 1360170606989 3125000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707245743/5000000000 : ℝ)^269 ≤ (44707015741363/100000000000000 : ℝ)^205 := by
    have hnat : (2707245743 : ℕ)^269*100000000000000^205 ≤ 44707015741363^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707245743 5000000000 44707015741363 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (489469989/2500000000 : ℝ)^269 ≤ (2941881205013/25000000000000 : ℝ)^205 := by
    have hnat : (489469989 : ℕ)^269*25000000000000^205 ≤ 2941881205013^205*2500000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489469989 2500000000 2941881205013 25000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663136467/1250000000 : ℝ), (2707245743/5000000000 : ℝ), (-489469989/2500000000 : ℝ)] ![(1360170606989/3125000000000 : ℝ), (44707015741363/100000000000000 : ℝ), (2941881205013/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663136467/1250000000 : ℝ)|^269 ≤ (1360170606989/3125000000000 : ℝ)^205
        have hw : |(663136467/1250000000 : ℝ)|=(663136467/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707245743/5000000000 : ℝ)|^269 ≤ (44707015741363/100000000000000 : ℝ)^205
        have hw : |(2707245743/5000000000 : ℝ)|=(2707245743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-489469989/2500000000 : ℝ)|^269 ≤ (2941881205013/25000000000000 : ℝ)^205
        have hw : |(-489469989/2500000000 : ℝ)|=(489469989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s4_7 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2162974703/5000000000 : ℝ)*x 0 + (2254614321/5000000000 : ℝ)*x 1 + (4149700143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2162974703/5000000000 : ℝ)^269 ≤ (33301809745543/100000000000000 : ℝ)^205 := by
    have hnat : (2162974703 : ℕ)^269*100000000000000^205 ≤ 33301809745543^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162974703 5000000000 33301809745543 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2254614321/5000000000 : ℝ)^269 ≤ (17582663847743/50000000000000 : ℝ)^205 := by
    have hnat : (2254614321 : ℕ)^269*50000000000000^205 ≤ 17582663847743^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254614321 5000000000 17582663847743 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4149700143/10000000000 : ℝ)^269 ≤ (31532862550693/100000000000000 : ℝ)^205 := by
    have hnat : (4149700143 : ℕ)^269*100000000000000^205 ≤ 31532862550693^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4149700143 10000000000 31532862550693 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2162974703/5000000000 : ℝ), (2254614321/5000000000 : ℝ), (4149700143/10000000000 : ℝ)] ![(33301809745543/100000000000000 : ℝ), (17582663847743/50000000000000 : ℝ), (31532862550693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2162974703/5000000000 : ℝ)|^269 ≤ (33301809745543/100000000000000 : ℝ)^205
        have hw : |(2162974703/5000000000 : ℝ)|=(2162974703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2254614321/5000000000 : ℝ)|^269 ≤ (17582663847743/50000000000000 : ℝ)^205
        have hw : |(2254614321/5000000000 : ℝ)|=(2254614321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4149700143/10000000000 : ℝ)|^269 ≤ (31532862550693/100000000000000 : ℝ)^205
        have hw : |(4149700143/10000000000 : ℝ)|=(4149700143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1344_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154807433/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (469/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1359/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (347/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14761/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (469/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1359/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (469/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1359/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (469/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1359/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (469/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1359/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (469/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1359/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (469/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1359/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1359/12500 : ℝ) ^ (4303/1024 : ℝ) ≤ (223033060238943/2500000000000000000 : ℝ) := by
    have hpowers : (1359/12500 : ℝ)^4303 ≤ (223033060238943/2500000000000000000 : ℝ)^1024 := by
      have hnat : (1359 : ℕ)^4303*2500000000000000000^1024 ≤ 223033060238943^1024*12500^4303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1359 12500 223033060238943 2500000000000000000 4303 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1359/12500 : ℝ)) (X := (223033060238943/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (469/3125 : ℝ) ^ (4303/1024 : ℝ) ≤ (34576913972430187/100000000000000000000 : ℝ) := by
    have hpowers : (469/3125 : ℝ)^4303 ≤ (34576913972430187/100000000000000000000 : ℝ)^1024 := by
      have hnat : (469 : ℕ)^4303*100000000000000000000^1024 ≤ 34576913972430187^1024*3125^4303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        469 3125 34576913972430187 100000000000000000000 4303 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (469/3125 : ℝ)) (X := (34576913972430187/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250223033060238943/1250000000000000000 : ℝ) ≤ (2500106144703227/2500000000000000 : ℝ) ^ (4303/1024 : ℝ) := by
    have hpowers : (1250223033060238943/1250000000000000000 : ℝ)^1024 ≤ (2500106144703227/2500000000000000 : ℝ)^4303 := by
      have hnat : (1250223033060238943 : ℕ)^1024*2500000000000000^4303 ≤ 2500106144703227^4303*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250223033060238943 1250000000000000000 2500106144703227 2500000000000000 1024 4303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500106144703227/2500000000000000 : ℝ)) (X := (1250223033060238943/1250000000000000000 : ℝ)) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100043498236381987907/100000000000000000000 : ℝ) ≤ (2000206994254161/2000000000000000 : ℝ) ^ (4303/1024 : ℝ) := by
    have hpowers : (100043498236381987907/100000000000000000000 : ℝ)^1024 ≤ (2000206994254161/2000000000000000 : ℝ)^4303 := by
      have hnat : (100043498236381987907 : ℕ)^1024*2000000000000000^4303 ≤ 2000206994254161^4303*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100043498236381987907 100000000000000000000 2000206994254161 2000000000000000 1024 4303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000206994254161/2000000000000000 : ℝ)) (X := (100043498236381987907/100000000000000000000 : ℝ)) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034576913972430187/50000000000000000000 : ℝ) ≤ (5000822681864351/5000000000000000 : ℝ) ^ (4303/1024 : ℝ) := by
    have hpowers : (50034576913972430187/50000000000000000000 : ℝ)^1024 ≤ (5000822681864351/5000000000000000 : ℝ)^4303 := by
      have hnat : (50034576913972430187 : ℕ)^1024*5000000000000000^4303 ≤ 5000822681864351^4303*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034576913972430187 50000000000000000000 5000822681864351 5000000000000000 1024 4303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000822681864351/5000000000000000 : ℝ)) (X := (50034576913972430187/50000000000000000000 : ℝ)) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(223033060238943/2500000000000000000 : ℝ) ≤ ((516856046054570939/517000000000000000 : ℝ)+2*(610392457897/413600000000000 : ℝ)*(1359/12500 : ℝ))^(4303/1024 : ℝ) := by
    rw [show (516856046054570939/517000000000000000 : ℝ)+2*(610392457897/413600000000000 : ℝ)*(1359/12500 : ℝ)=(2500106144703227/2500000000000000 : ℝ) by norm_num, show 1+2*(223033060238943/2500000000000000000 : ℝ)=(1250223033060238943/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34576913972430187/100000000000000000000 : ℝ)+(223033060238943/2500000000000000000 : ℝ) ≤ ((516856046054570939/517000000000000000 : ℝ)+(610392457897/413600000000000 : ℝ)*((469/3125 : ℝ)+(1359/12500 : ℝ)))^(4303/1024 : ℝ) := by
    rw [show (516856046054570939/517000000000000000 : ℝ)+(610392457897/413600000000000 : ℝ)*((469/3125 : ℝ)+(1359/12500 : ℝ))=(2000206994254161/2000000000000000 : ℝ) by norm_num, show 1+(34576913972430187/100000000000000000000 : ℝ)+(223033060238943/2500000000000000000 : ℝ)=(100043498236381987907/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34576913972430187/100000000000000000000 : ℝ) ≤ ((516856046054570939/517000000000000000 : ℝ)+2*(610392457897/413600000000000 : ℝ)*(469/3125 : ℝ))^(4303/1024 : ℝ) := by
    rw [show (516856046054570939/517000000000000000 : ℝ)+2*(610392457897/413600000000000 : ℝ)*(469/3125 : ℝ)=(5000822681864351/5000000000000000 : ℝ) by norm_num, show 1+2*(34576913972430187/100000000000000000000 : ℝ)=(50034576913972430187/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (516856046054570939/517000000000000000 : ℝ)*(X 1 0+X 2 0)+(610392457897/413600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4303/1024 : ℝ)) (lo := (1359/12500 : ℝ)) (hi := (469/3125 : ℝ)) (c := (516856046054570939/517000000000000000 : ℝ)) (alpha := (610392457897/413600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (516856046054570939/517000000000000000 : ℝ)*(X 0 1+X 2 1)+(610392457897/413600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4303/1024 : ℝ)) (lo := (1359/12500 : ℝ)) (hi := (469/3125 : ℝ)) (c := (516856046054570939/517000000000000000 : ℝ)) (alpha := (610392457897/413600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (516856046054570939/517000000000000000 : ℝ)*(X 0 2+X 1 2)+(610392457897/413600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4303/1024 : ℝ)) (lo := (1359/12500 : ℝ)) (hi := (469/3125 : ℝ)) (c := (516856046054570939/517000000000000000 : ℝ)) (alpha := (610392457897/413600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2041948811/10000000000 : ℝ)*X 0 0+(1083026271/2000000000 : ℝ)*X 0 1+(5242336527/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674805023/5000000000 : ℝ)*X 1 0+(-2130034961/10000000000 : ℝ)*X 1 1+(5242336503/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349610147/10000000000 : ℝ)*X 2 0+(5242336361/10000000000 : ℝ)*X 2 1+(-1065017507/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2162960719/5000000000 : ℝ)*X 0 0+(4148359001/10000000000 : ℝ)*X 0 1+(4510562921/10000000000 : ℝ)*X 0 2+(2162960719/5000000000 : ℝ)*X 1 0+(4148359001/10000000000 : ℝ)*X 1 1+(4510562921/10000000000 : ℝ)*X 1 2+(2162960719/5000000000 : ℝ)*X 2 0+(4148359001/10000000000 : ℝ)*X 2 1+(4510562921/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1020981069/5000000000 : ℝ)*X 0 0+(2621486409/5000000000 : ℝ)*X 0 1+(270724581/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305091931/10000000000 : ℝ)*X 1 0+(-1957879829/10000000000 : ℝ)*X 1 1+(1082898277/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663136467/1250000000 : ℝ)*X 2 0+(2707245743/5000000000 : ℝ)*X 2 1+(-489469989/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2162974703/5000000000 : ℝ)*X 0 0+(2254614321/5000000000 : ℝ)*X 0 1+(4149700143/10000000000 : ℝ)*X 0 2+(2162974703/5000000000 : ℝ)*X 1 0+(2254614321/5000000000 : ℝ)*X 1 1+(4149700143/10000000000 : ℝ)*X 1 2+(2162974703/5000000000 : ℝ)*X 2 0+(2254614321/5000000000 : ℝ)*X 2 1+(4149700143/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12882549969971001422682993/3231250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (349972073/100000000000000 : ℝ)*(base19) + (393601139/100000000000000 : ℝ)*(base23) + (44102141/100000000000000 : ℝ)*(lower2) + (46465023/50000000000000 : ℝ)*(upper3) + (4495541/50000000000000 : ℝ)*(lower4) + (534256320100893/12500000000000 : ℝ)*(major0) + (534256320100893/12500000000000 : ℝ)*(major1) + (534256320100893/12500000000000 : ℝ)*(major2) + (1446803879074237/25000000000000 : ℝ)*(sp0) + (2893609316644813/50000000000000 : ℝ)*(sp1) + (5787218589660561/100000000000000 : ℝ)*(sp2) + (172554865502447/6250000000000 : ℝ)*(sp3) + (216685297/6250000000000 : ℝ)*(sp4) + (831483601/20000000000000 : ℝ)*(sp7) + (2760882005457157/100000000000000 : ℝ)*(f.failure) + (57872189832617/1000000000000 : ℝ)*(f.sum) + (8875210998149/2585000000000000000000000000 : ℝ)*base66 + (65399798362300223/6462500000000000000000000000000 : ℝ)*base68 + (54538491138362723/6462500000000000000000000000000 : ℝ)*base70 + (53279743864650223/6462500000000000000000000000000 : ℝ)*base72 + (3255381638939/2585000000000000000000000000 : ℝ)*base74 + (32130548159787723/6462500000000000000000000000000 : ℝ)*base76 + (73534056863487723/6462500000000000000000000000000 : ℝ)*base78 + (164096667748112723/6462500000000000000000000000000 : ℝ)*base80 + (36281013377/323125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (66647981/10000000000000000000000 : ℝ)*base89 + (66647981/10000000000000000000000 : ℝ)*base91 + (66647981/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2927051211131865745797579/1175000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (127138981/20000000000000 : ℝ)*(base19) + (116617231/25000000000000 : ℝ)*(base23) + (11054759/50000000000000 : ℝ)*(upper3) + (52173371/100000000000000 : ℝ)*(lower4) + (31117671/25000000000000 : ℝ)*(upper5) + (2152920814687819/50000000000000 : ℝ)*(major0) + (2152920814687819/50000000000000 : ℝ)*(major1) + (2152920814687819/50000000000000 : ℝ)*(major2) + (3844726691/50000000000000 : ℝ)*(sp1) + (1341658493/100000000000000 : ℝ)*(sp2) + (5830265290324031/100000000000000 : ℝ)*(sp4) + (91097765080871/1562500000000 : ℝ)*(sp5) + (2915131741098307/50000000000000 : ℝ)*(sp6) + (1390708942695161/50000000000000 : ℝ)*(sp7) + (1390708942695161/50000000000000 : ℝ)*(f.failure) + (5830265290324031/100000000000000 : ℝ)*(f.sum) + (5697301985247/940000000000000000000000000 : ℝ)*base66 + (3494513338564019/2350000000000000000000000000000 : ℝ)*base68 + (37591942170964019/2350000000000000000000000000000 : ℝ)*base70 + (41043879970664019/2350000000000000000000000000000 : ℝ)*base72 + (343009806273/940000000000000000000000000 : ℝ)*base73 + (38861525831064019/2350000000000000000000000000000 : ℝ)*base76 + (17386225847314019/2350000000000000000000000000000 : ℝ)*base78 + (22374890433214019/2350000000000000000000000000000 : ℝ)*base80 + (1948170928887/940000000000000000000000000 : ℝ)*base82 + (75931713/5000000000000000000000 : ℝ)*base89 + (75931713/5000000000000000000000 : ℝ)*base91 + (75931713/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1344_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154807433/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (469/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1359/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (347/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14761/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1344_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1344_s5_0 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2042198179/10000000000 : ℝ)*x 0 + (1082596481/2000000000 : ℝ)*x 1 + (5244321307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2042198179/10000000000 : ℝ)^269 ≤ (2487389548701/20000000000000 : ℝ)^205 := by
    have hnat : (2042198179 : ℕ)^269*20000000000000^205 ≤ 2487389548701^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2042198179 10000000000 2487389548701 20000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082596481/2000000000 : ℝ)^269 ≤ (22345333015191/50000000000000 : ℝ)^205 := by
    have hnat : (1082596481 : ℕ)^269*50000000000000^205 ≤ 22345333015191^205*2000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082596481 2000000000 22345333015191 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244321307/10000000000 : ℝ)^269 ≤ (42872386211641/100000000000000 : ℝ)^205 := by
    have hnat : (5244321307 : ℕ)^269*100000000000000^205 ≤ 42872386211641^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244321307 10000000000 42872386211641 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2042198179/10000000000 : ℝ), (1082596481/2000000000 : ℝ), (5244321307/10000000000 : ℝ)] ![(2487389548701/20000000000000 : ℝ), (22345333015191/50000000000000 : ℝ), (42872386211641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2042198179/10000000000 : ℝ)|^269 ≤ (2487389548701/20000000000000 : ℝ)^205
        have hw : |(-2042198179/10000000000 : ℝ)|=(2042198179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082596481/2000000000 : ℝ)|^269 ≤ (22345333015191/50000000000000 : ℝ)^205
        have hw : |(1082596481/2000000000 : ℝ)|=(1082596481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244321307/10000000000 : ℝ)|^269 ≤ (42872386211641/100000000000000 : ℝ)^205
        have hw : |(5244321307/10000000000 : ℝ)|=(5244321307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s5_1 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5349060781/10000000000 : ℝ)*x 0 + (-2128137513/10000000000 : ℝ)*x 1 + (1311080327/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349060781/10000000000 : ℝ)^269 ≤ (1374982357287/3125000000000 : ℝ)^205 := by
    have hnat : (5349060781 : ℕ)^269*3125000000000^205 ≤ 1374982357287^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349060781 10000000000 1374982357287 3125000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2128137513/10000000000 : ℝ)^269 ≤ (32820445833/250000000000 : ℝ)^205 := by
    have hnat : (2128137513 : ℕ)^269*250000000000^205 ≤ 32820445833^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128137513 10000000000 32820445833 250000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311080327/2500000000 : ℝ)^269 ≤ (42872386222369/100000000000000 : ℝ)^205 := by
    have hnat : (1311080327 : ℕ)^269*100000000000000^205 ≤ 42872386222369^205*2500000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311080327 2500000000 42872386222369 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349060781/10000000000 : ℝ), (-2128137513/10000000000 : ℝ), (1311080327/2500000000 : ℝ)] ![(1374982357287/3125000000000 : ℝ), (32820445833/250000000000 : ℝ), (42872386222369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349060781/10000000000 : ℝ)|^269 ≤ (1374982357287/3125000000000 : ℝ)^205
        have hw : |(5349060781/10000000000 : ℝ)|=(5349060781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2128137513/10000000000 : ℝ)|^269 ≤ (32820445833/250000000000 : ℝ)^205
        have hw : |(-2128137513/10000000000 : ℝ)|=(2128137513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311080327/2500000000 : ℝ)|^269 ≤ (42872386222369/100000000000000 : ℝ)^205
        have hw : |(1311080327/2500000000 : ℝ)|=(1311080327/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s5_2 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5349060793/10000000000 : ℝ)*x 0 + (5244321313/10000000000 : ℝ)*x 1 + (-2128137491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349060793/10000000000 : ℝ)^269 ≤ (10999858890677/25000000000000 : ℝ)^205 := by
    have hnat : (5349060793 : ℕ)^269*25000000000000^205 ≤ 10999858890677^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349060793 10000000000 10999858890677 25000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244321313/10000000000 : ℝ)^269 ≤ (8574477255201/20000000000000 : ℝ)^205 := by
    have hnat : (5244321313 : ℕ)^269*20000000000000^205 ≤ 8574477255201^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244321313 10000000000 8574477255201 20000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2128137491/10000000000 : ℝ)^269 ≤ (3282044538779/25000000000000 : ℝ)^205 := by
    have hnat : (2128137491 : ℕ)^269*25000000000000^205 ≤ 3282044538779^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128137491 10000000000 3282044538779 25000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349060793/10000000000 : ℝ), (5244321313/10000000000 : ℝ), (-2128137491/10000000000 : ℝ)] ![(10999858890677/25000000000000 : ℝ), (8574477255201/20000000000000 : ℝ), (3282044538779/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349060793/10000000000 : ℝ)|^269 ≤ (10999858890677/25000000000000 : ℝ)^205
        have hw : |(5349060793/10000000000 : ℝ)|=(5349060793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244321313/10000000000 : ℝ)|^269 ≤ (8574477255201/20000000000000 : ℝ)^205
        have hw : |(5244321313/10000000000 : ℝ)|=(5244321313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2128137491/10000000000 : ℝ)|^269 ≤ (3282044538779/25000000000000 : ℝ)^205
        have hw : |(-2128137491/10000000000 : ℝ)|=(2128137491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s5_3 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4326070281/10000000000 : ℝ)*x 0 + (4152673121/10000000000 : ℝ)*x 1 + (4506211833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4326070281/10000000000 : ℝ)^269 ≤ (3330303076673/10000000000000 : ℝ)^205 := by
    have hnat : (4326070281 : ℕ)^269*10000000000000^205 ≤ 3330303076673^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4326070281 10000000000 3330303076673 10000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4152673121/10000000000 : ℝ)^269 ≤ (15781254932387/50000000000000 : ℝ)^205 := by
    have hnat : (4152673121 : ℕ)^269*50000000000000^205 ≤ 15781254932387^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4152673121 10000000000 15781254932387 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4506211833/10000000000 : ℝ)^269 ≤ (35134459355037/100000000000000 : ℝ)^205 := by
    have hnat : (4506211833 : ℕ)^269*100000000000000^205 ≤ 35134459355037^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506211833 10000000000 35134459355037 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4326070281/10000000000 : ℝ), (4152673121/10000000000 : ℝ), (4506211833/10000000000 : ℝ)] ![(3330303076673/10000000000000 : ℝ), (15781254932387/50000000000000 : ℝ), (35134459355037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4326070281/10000000000 : ℝ)|^269 ≤ (3330303076673/10000000000000 : ℝ)^205
        have hw : |(4326070281/10000000000 : ℝ)|=(4326070281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4152673121/10000000000 : ℝ)|^269 ≤ (15781254932387/50000000000000 : ℝ)^205
        have hw : |(4152673121/10000000000 : ℝ)|=(4152673121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4506211833/10000000000 : ℝ)|^269 ≤ (35134459355037/100000000000000 : ℝ)^205
        have hw : |(4506211833/10000000000 : ℝ)|=(4506211833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s5_4 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2042210501/10000000000 : ℝ)*x 0 + (2622463921/5000000000 : ℝ)*x 1 + (1353093181/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2042210501/10000000000 : ℝ)^269 ≤ (2487409242339/20000000000000 : ℝ)^205 := by
    have hnat : (2042210501 : ℕ)^269*20000000000000^205 ≤ 2487409242339^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2042210501 10000000000 2487409242339 20000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622463921/5000000000 : ℝ)^269 ≤ (4287889275743/10000000000000 : ℝ)^205 := by
    have hnat : (2622463921 : ℕ)^269*10000000000000^205 ≤ 4287889275743^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622463921 5000000000 4287889275743 10000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353093181/2500000000 : ℝ)^269 ≤ (44684061017703/100000000000000 : ℝ)^205 := by
    have hnat : (1353093181 : ℕ)^269*100000000000000^205 ≤ 44684061017703^205*2500000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353093181 2500000000 44684061017703 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2042210501/10000000000 : ℝ), (2622463921/5000000000 : ℝ), (1353093181/2500000000 : ℝ)] ![(2487409242339/20000000000000 : ℝ), (4287889275743/10000000000000 : ℝ), (44684061017703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2042210501/10000000000 : ℝ)|^269 ≤ (2487409242339/20000000000000 : ℝ)^205
        have hw : |(-2042210501/10000000000 : ℝ)|=(2042210501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622463921/5000000000 : ℝ)|^269 ≤ (4287889275743/10000000000000 : ℝ)^205
        have hw : |(2622463921/5000000000 : ℝ)|=(2622463921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353093181/2500000000 : ℝ)|^269 ≤ (44684061017703/100000000000000 : ℝ)^205
        have hw : |(1353093181/2500000000 : ℝ)|=(1353093181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s5_5 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1326401869/2500000000 : ℝ)*x 0 + (-122505379/625000000 : ℝ)*x 1 + (2706186371/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326401869/2500000000 : ℝ)^269 ≤ (8706202378909/20000000000000 : ℝ)^205 := by
    have hnat : (1326401869 : ℕ)^269*20000000000000^205 ≤ 8706202378909^205*2500000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326401869 2500000000 8706202378909 20000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (122505379/625000000 : ℝ)^269 ≤ (11784926878061/100000000000000 : ℝ)^205 := by
    have hnat : (122505379 : ℕ)^269*100000000000000^205 ≤ 11784926878061^205*625000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122505379 625000000 11784926878061 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706186371/5000000000 : ℝ)^269 ≤ (1396376912897/3125000000000 : ℝ)^205 := by
    have hnat : (2706186371 : ℕ)^269*3125000000000^205 ≤ 1396376912897^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706186371 5000000000 1396376912897 3125000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326401869/2500000000 : ℝ), (-122505379/625000000 : ℝ), (2706186371/5000000000 : ℝ)] ![(8706202378909/20000000000000 : ℝ), (11784926878061/100000000000000 : ℝ), (1396376912897/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326401869/2500000000 : ℝ)|^269 ≤ (8706202378909/20000000000000 : ℝ)^205
        have hw : |(1326401869/2500000000 : ℝ)|=(1326401869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-122505379/625000000 : ℝ)|^269 ≤ (11784926878061/100000000000000 : ℝ)^205
        have hw : |(-122505379/625000000 : ℝ)|=(122505379/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706186371/5000000000 : ℝ)|^269 ≤ (1396376912897/3125000000000 : ℝ)^205
        have hw : |(2706186371/5000000000 : ℝ)|=(2706186371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s5_6 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5305607451/10000000000 : ℝ)*x 0 + (5412372767/10000000000 : ℝ)*x 1 + (-392017213/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305607451/10000000000 : ℝ)^269 ≤ (43531011625391/100000000000000 : ℝ)^205 := by
    have hnat : (5305607451 : ℕ)^269*100000000000000^205 ≤ 43531011625391^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305607451 10000000000 43531011625391 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412372767/10000000000 : ℝ)^269 ≤ (22342030741769/50000000000000 : ℝ)^205 := by
    have hnat : (5412372767 : ℕ)^269*50000000000000^205 ≤ 22342030741769^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412372767 10000000000 22342030741769 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (392017213/2000000000 : ℝ)^269 ≤ (11784926885951/100000000000000 : ℝ)^205 := by
    have hnat : (392017213 : ℕ)^269*100000000000000^205 ≤ 11784926885951^205*2000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      392017213 2000000000 11784926885951 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305607451/10000000000 : ℝ), (5412372767/10000000000 : ℝ), (-392017213/2000000000 : ℝ)] ![(43531011625391/100000000000000 : ℝ), (22342030741769/50000000000000 : ℝ), (11784926885951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305607451/10000000000 : ℝ)|^269 ≤ (43531011625391/100000000000000 : ℝ)^205
        have hw : |(5305607451/10000000000 : ℝ)|=(5305607451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412372767/10000000000 : ℝ)|^269 ≤ (22342030741769/50000000000000 : ℝ)^205
        have hw : |(5412372767/10000000000 : ℝ)|=(5412372767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-392017213/2000000000 : ℝ)|^269 ≤ (11784926885951/100000000000000 : ℝ)^205
        have hw : |(-392017213/2000000000 : ℝ)|=(392017213/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s5_7 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2163048019/5000000000 : ℝ)*x 0 + (180197621/400000000 : ℝ)*x 1 + (1038487767/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163048019/5000000000 : ℝ)^269 ≤ (8325822738237/25000000000000 : ℝ)^205 := by
    have hnat : (2163048019 : ℕ)^269*25000000000000^205 ≤ 8325822738237^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163048019 5000000000 8325822738237 25000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (180197621/400000000 : ℝ)^269 ≤ (17560726557831/50000000000000 : ℝ)^205 := by
    have hnat : (180197621 : ℕ)^269*50000000000000^205 ≤ 17560726557831^205*400000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180197621 400000000 17560726557831 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1038487767/2500000000 : ℝ)^269 ≤ (126301023693/400000000000 : ℝ)^205 := by
    have hnat : (1038487767 : ℕ)^269*400000000000^205 ≤ 126301023693^205*2500000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038487767 2500000000 126301023693 400000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2163048019/5000000000 : ℝ), (180197621/400000000 : ℝ), (1038487767/2500000000 : ℝ)] ![(8325822738237/25000000000000 : ℝ), (17560726557831/50000000000000 : ℝ), (126301023693/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2163048019/5000000000 : ℝ)|^269 ≤ (8325822738237/25000000000000 : ℝ)^205
        have hw : |(2163048019/5000000000 : ℝ)|=(2163048019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(180197621/400000000 : ℝ)|^269 ≤ (17560726557831/50000000000000 : ℝ)^205
        have hw : |(180197621/400000000 : ℝ)|=(180197621/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1038487767/2500000000 : ℝ)|^269 ≤ (126301023693/400000000000 : ℝ)^205
        have hw : |(1038487767/2500000000 : ℝ)|=(1038487767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1344_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154807433/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14761/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (347/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (5573/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3679/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14761/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (347/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14761/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (347/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14761/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (347/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14761/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (347/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14761/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (347/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14761/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (347/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (347/3125 : ℝ) ^ (4303/1024 : ℝ) ≤ (1218633151246269/12500000000000000000 : ℝ) := by
    have hpowers : (347/3125 : ℝ)^4303 ≤ (1218633151246269/12500000000000000000 : ℝ)^1024 := by
      have hnat : (347 : ℕ)^4303*12500000000000000000^1024 ≤ 1218633151246269^1024*3125^4303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        347 3125 1218633151246269 12500000000000000000 4303 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (347/3125 : ℝ)) (X := (1218633151246269/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14761/100000 : ℝ) ^ (4303/1024 : ℝ) ≤ (32247880379569287/100000000000000000000 : ℝ) := by
    have hpowers : (14761/100000 : ℝ)^4303 ≤ (32247880379569287/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14761 : ℕ)^4303*100000000000000000000^1024 ≤ 32247880379569287^1024*100000^4303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14761 100000 32247880379569287 100000000000000000000 4303 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14761/100000 : ℝ)) (X := (32247880379569287/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251218633151246269/6250000000000000000 : ℝ) ≤ (2000092793876041/2000000000000000 : ℝ) ^ (4303/1024 : ℝ) := by
    have hpowers : (6251218633151246269/6250000000000000000 : ℝ)^1024 ≤ (2000092793876041/2000000000000000 : ℝ)^4303 := by
      have hnat : (6251218633151246269 : ℕ)^1024*2000000000000000^4303 ≤ 2000092793876041^4303*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251218633151246269 6250000000000000000 2000092793876041 2000000000000000 1024 4303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000092793876041/2000000000000000 : ℝ)) (X := (6251218633151246269/6250000000000000000 : ℝ)) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100041996945589539439/100000000000000000000 : ℝ) ≤ (10000999256160869/10000000000000000 : ℝ) ^ (4303/1024 : ℝ) := by
    have hpowers : (100041996945589539439/100000000000000000000 : ℝ)^1024 ≤ (10000999256160869/10000000000000000 : ℝ)^4303 := by
      have hnat : (100041996945589539439 : ℕ)^1024*10000000000000000^4303 ≤ 10000999256160869^4303*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100041996945589539439 100000000000000000000 10000999256160869 10000000000000000 1024 4303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000999256160869/10000000000000000 : ℝ)) (X := (100041996945589539439/100000000000000000000 : ℝ)) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032247880379569287/50000000000000000000 : ℝ) ≤ (10001534542941533/10000000000000000 : ℝ) ^ (4303/1024 : ℝ) := by
    have hpowers : (50032247880379569287/50000000000000000000 : ℝ)^1024 ≤ (10001534542941533/10000000000000000 : ℝ)^4303 := by
      have hnat : (50032247880379569287 : ℕ)^1024*10000000000000000^4303 ≤ 10001534542941533^4303*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032247880379569287 50000000000000000000 10001534542941533 10000000000000000 1024 4303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001534542941533/10000000000000000 : ℝ)) (X := (50032247880379569287/50000000000000000000 : ℝ)) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1218633151246269/12500000000000000000 : ℝ) ≤ ((12186603029066141191/12190000000000000000 : ℝ)+2*(22303615861/15237500000000 : ℝ)*(347/3125 : ℝ))^(4303/1024 : ℝ) := by
    rw [show (12186603029066141191/12190000000000000000 : ℝ)+2*(22303615861/15237500000000 : ℝ)*(347/3125 : ℝ)=(2000092793876041/2000000000000000 : ℝ) by norm_num, show 1+2*(1218633151246269/12500000000000000000 : ℝ)=(6251218633151246269/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32247880379569287/100000000000000000000 : ℝ)+(1218633151246269/12500000000000000000 : ℝ) ≤ ((12186603029066141191/12190000000000000000 : ℝ)+(22303615861/15237500000000 : ℝ)*((14761/100000 : ℝ)+(347/3125 : ℝ)))^(4303/1024 : ℝ) := by
    rw [show (12186603029066141191/12190000000000000000 : ℝ)+(22303615861/15237500000000 : ℝ)*((14761/100000 : ℝ)+(347/3125 : ℝ))=(10000999256160869/10000000000000000 : ℝ) by norm_num, show 1+(32247880379569287/100000000000000000000 : ℝ)+(1218633151246269/12500000000000000000 : ℝ)=(100041996945589539439/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32247880379569287/100000000000000000000 : ℝ) ≤ ((12186603029066141191/12190000000000000000 : ℝ)+2*(22303615861/15237500000000 : ℝ)*(14761/100000 : ℝ))^(4303/1024 : ℝ) := by
    rw [show (12186603029066141191/12190000000000000000 : ℝ)+2*(22303615861/15237500000000 : ℝ)*(14761/100000 : ℝ)=(10001534542941533/10000000000000000 : ℝ) by norm_num, show 1+2*(32247880379569287/100000000000000000000 : ℝ)=(50032247880379569287/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12186603029066141191/12190000000000000000 : ℝ)*(X 1 0+X 2 0)+(22303615861/15237500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4303/1024 : ℝ)) (lo := (347/3125 : ℝ)) (hi := (14761/100000 : ℝ)) (c := (12186603029066141191/12190000000000000000 : ℝ)) (alpha := (22303615861/15237500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12186603029066141191/12190000000000000000 : ℝ)*(X 0 1+X 2 1)+(22303615861/15237500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4303/1024 : ℝ)) (lo := (347/3125 : ℝ)) (hi := (14761/100000 : ℝ)) (c := (12186603029066141191/12190000000000000000 : ℝ)) (alpha := (22303615861/15237500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12186603029066141191/12190000000000000000 : ℝ)*(X 0 2+X 1 2)+(22303615861/15237500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4303/1024 : ℝ)) (lo := (347/3125 : ℝ)) (hi := (14761/100000 : ℝ)) (c := (12186603029066141191/12190000000000000000 : ℝ)) (alpha := (22303615861/15237500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2042198179/10000000000 : ℝ)*X 0 0+(1082596481/2000000000 : ℝ)*X 0 1+(5244321307/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349060781/10000000000 : ℝ)*X 1 0+(-2128137513/10000000000 : ℝ)*X 1 1+(1311080327/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349060793/10000000000 : ℝ)*X 2 0+(5244321313/10000000000 : ℝ)*X 2 1+(-2128137491/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4326070281/10000000000 : ℝ)*X 0 0+(4152673121/10000000000 : ℝ)*X 0 1+(4506211833/10000000000 : ℝ)*X 0 2+(4326070281/10000000000 : ℝ)*X 1 0+(4152673121/10000000000 : ℝ)*X 1 1+(4506211833/10000000000 : ℝ)*X 1 2+(4326070281/10000000000 : ℝ)*X 2 0+(4152673121/10000000000 : ℝ)*X 2 1+(4506211833/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2042210501/10000000000 : ℝ)*X 0 0+(2622463921/5000000000 : ℝ)*X 0 1+(1353093181/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326401869/2500000000 : ℝ)*X 1 0+(-122505379/625000000 : ℝ)*X 1 1+(2706186371/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305607451/10000000000 : ℝ)*X 2 0+(5412372767/10000000000 : ℝ)*X 2 1+(-392017213/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2163048019/5000000000 : ℝ)*X 0 0+(180197621/400000000 : ℝ)*X 0 1+(1038487767/2500000000 : ℝ)*X 0 2+(2163048019/5000000000 : ℝ)*X 1 0+(180197621/400000000 : ℝ)*X 1 1+(1038487767/2500000000 : ℝ)*X 1 2+(2163048019/5000000000 : ℝ)*X 2 0+(180197621/400000000 : ℝ)*X 2 1+(1038487767/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2032310421146213002065233259/304750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1276113647/100000000000000 : ℝ)*(base19) + (1211459463/100000000000000 : ℝ)*(base23) + (41698837/100000000000000 : ℝ)*(lower2) + (162309059/100000000000000 : ℝ)*(upper3) + (67153931/50000000000000 : ℝ)*(upper5) + (2189418051092017/50000000000000 : ℝ)*(major0) + (2189418051092017/50000000000000 : ℝ)*(major1) + (2189418051092017/50000000000000 : ℝ)*(major2) + (741134477362579/12500000000000 : ℝ)*(sp0) + (1482275258111859/25000000000000 : ℝ)*(sp1) + (5929101097101621/100000000000000 : ℝ)*(sp2) + (1414278341604727/50000000000000 : ℝ)*(sp3) + (6622415113/25000000000000 : ℝ)*(sp4) + (1623788111/12500000000000 : ℝ)*(sp7) + (1414284836757171/50000000000000 : ℝ)*(f.failure) + (1482275577140271/25000000000000 : ℝ)*(f.sum) + (7031393210959/3047500000000000000000000000 : ℝ)*base66 + (240651917923572247/609500000000000000000000000000000 : ℝ)*base67 + (5948064675403572247/609500000000000000000000000000000 : ℝ)*base69 + (6459367523341572247/609500000000000000000000000000000 : ℝ)*base71 + (13209825295461/3047500000000000000000000000 : ℝ)*base73 + (1283707079848427753/609500000000000000000000000000000 : ℝ)*base76 + (1293100500740072247/609500000000000000000000000000000 : ℝ)*base77 + (3572784685851927753/609500000000000000000000000000000 : ℝ)*base80 + (19379247893967/6095000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (13147957/5000000000000000000000 : ℝ)*base90 + (13147957/5000000000000000000000 : ℝ)*base92 + (13147957/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6020073673188154097661/3047500000000000000000000000 : ℝ) := by norm_num
    linear_combination (179244759/50000000000000 : ℝ)*(base19) + (71656151/20000000000000 : ℝ)*(base23) + (2679611/25000000000000 : ℝ)*(upper2) + (58007399/100000000000000 : ℝ)*(upper3) + (17796051/50000000000000 : ℝ)*(upper5) + (2205300459489539/50000000000000 : ℝ)*(major0) + (2205300459489539/50000000000000 : ℝ)*(major1) + (2205300459489539/50000000000000 : ℝ)*(major2) + (348714769/5000000000000 : ℝ)*(sp1) + (3959038997/50000000000000 : ℝ)*(sp2) + (2986056588179621/50000000000000 : ℝ)*(sp4) + (746513230446793/12500000000000 : ℝ)*(sp5) + (2986052450000247/50000000000000 : ℝ)*(sp6) + (142454429787589/5000000000000 : ℝ)*(sp7) + (142454429787589/5000000000000 : ℝ)*(f.failure) + (2986056588179621/50000000000000 : ℝ)*(f.sum) + (6592978879227/3047500000000000000000000000 : ℝ)*base65 + (1266688662083299051/609500000000000000000000000000000 : ℝ)*base68 + (2519881295668700949/609500000000000000000000000000000 : ℝ)*base69 + (2893310416366700949/609500000000000000000000000000000 : ℝ)*base71 + (1420096694151/380937500000000000000000000 : ℝ)*base74 + (7450752703408700949/609500000000000000000000000000000 : ℝ)*base75 + (846509974697299051/609500000000000000000000000000000 : ℝ)*base78 + (890515779615299051/609500000000000000000000000000000 : ℝ)*base80 + (3086902308739/1523750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (1650963/500000000000000000000 : ℝ)*base90 + (1650963/500000000000000000000 : ℝ)*base92 + (1650963/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1344_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154807433/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14761/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (347/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5573/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3679/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1344_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1344_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154807433/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (503/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1973/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5573/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3679/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1344_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1344_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1344_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154807433/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (503/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1973/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5573/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3679/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1344_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

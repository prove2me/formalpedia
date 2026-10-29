-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1516_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:56:26.004095+00:00
-- url     : https://prove2.me/submissions/9b8ecb70-e072-4a2a-9c47-7613c87132c7

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
theorem support_rectangle_w1516_s0_0 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1681599913/10000000000 : ℝ)*x 0 + (5909755289/10000000000 : ℝ)*x 1 + (121425609/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1681599913/10000000000 : ℝ)^4529 ≤ (2497206270783/25000000000000 : ℝ)^3505 := by
    have hnat : (1681599913 : ℕ)^4529*25000000000000^3505 ≤ 2497206270783^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1681599913 10000000000 2497206270783 25000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5909755289/10000000000 : ℝ)^4529 ≤ (50679532278697/100000000000000 : ℝ)^3505 := by
    have hnat : (5909755289 : ℕ)^4529*100000000000000^3505 ≤ 50679532278697^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5909755289 10000000000 50679532278697 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (121425609/250000000 : ℝ)^4529 ≤ (39331642616517/100000000000000 : ℝ)^3505 := by
    have hnat : (121425609 : ℕ)^4529*100000000000000^3505 ≤ 39331642616517^3505*250000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121425609 250000000 39331642616517 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1681599913/10000000000 : ℝ), (5909755289/10000000000 : ℝ), (121425609/250000000 : ℝ)] ![(2497206270783/25000000000000 : ℝ), (50679532278697/100000000000000 : ℝ), (39331642616517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1681599913/10000000000 : ℝ)|^4529 ≤ (2497206270783/25000000000000 : ℝ)^3505
        have hw : |(-1681599913/10000000000 : ℝ)|=(1681599913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5909755289/10000000000 : ℝ)|^4529 ≤ (50679532278697/100000000000000 : ℝ)^3505
        have hw : |(5909755289/10000000000 : ℝ)|=(5909755289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(121425609/250000000 : ℝ)|^4529 ≤ (39331642616517/100000000000000 : ℝ)^3505
        have hw : |(121425609/250000000 : ℝ)|=(121425609/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_s0_1 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (342319387/625000000 : ℝ)*x 0 + (-2271372261/10000000000 : ℝ)*x 1 + (18972751/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (342319387/625000000 : ℝ)^4529 ≤ (45937592391919/100000000000000 : ℝ)^3505 := by
    have hnat : (342319387 : ℕ)^4529*100000000000000^3505 ≤ 45937592391919^3505*625000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342319387 625000000 45937592391919 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2271372261/10000000000 : ℝ)^4529 ≤ (14730766063127/100000000000000 : ℝ)^3505 := by
    have hnat : (2271372261 : ℕ)^4529*100000000000000^3505 ≤ 14730766063127^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2271372261 10000000000 14730766063127 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (18972751/39062500 : ℝ)^4529 ≤ (3933164152829/10000000000000 : ℝ)^3505 := by
    have hnat : (18972751 : ℕ)^4529*10000000000000^3505 ≤ 3933164152829^3505*39062500^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18972751 39062500 3933164152829 10000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(342319387/625000000 : ℝ), (-2271372261/10000000000 : ℝ), (18972751/39062500 : ℝ)] ![(45937592391919/100000000000000 : ℝ), (14730766063127/100000000000000 : ℝ), (3933164152829/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(342319387/625000000 : ℝ)|^4529 ≤ (45937592391919/100000000000000 : ℝ)^3505
        have hw : |(342319387/625000000 : ℝ)|=(342319387/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2271372261/10000000000 : ℝ)|^4529 ≤ (14730766063127/100000000000000 : ℝ)^3505
        have hw : |(-2271372261/10000000000 : ℝ)|=(2271372261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(18972751/39062500 : ℝ)|^4529 ≤ (3933164152829/10000000000000 : ℝ)^3505
        have hw : |(18972751/39062500 : ℝ)|=(18972751/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_s0_2 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (342319393/625000000 : ℝ)*x 0 + (48570243/100000000 : ℝ)*x 1 + (-1135686041/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (342319393/625000000 : ℝ)^4529 ≤ (45937593432323/100000000000000 : ℝ)^3505 := by
    have hnat : (342319393 : ℕ)^4529*100000000000000^3505 ≤ 45937593432323^3505*625000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342319393 625000000 45937593432323 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (48570243/100000000 : ℝ)^4529 ≤ (19665820994347/50000000000000 : ℝ)^3505 := by
    have hnat : (48570243 : ℕ)^4529*50000000000000^3505 ≤ 19665820994347^3505*100000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48570243 100000000 19665820994347 50000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1135686041/5000000000 : ℝ)^4529 ≤ (7365382281541/50000000000000 : ℝ)^3505 := by
    have hnat : (1135686041 : ℕ)^4529*50000000000000^3505 ≤ 7365382281541^3505*5000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135686041 5000000000 7365382281541 50000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(342319393/625000000 : ℝ), (48570243/100000000 : ℝ), (-1135686041/5000000000 : ℝ)] ![(45937593432323/100000000000000 : ℝ), (19665820994347/50000000000000 : ℝ), (7365382281541/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(342319393/625000000 : ℝ)|^4529 ≤ (45937593432323/100000000000000 : ℝ)^3505
        have hw : |(342319393/625000000 : ℝ)|=(342319393/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(48570243/100000000 : ℝ)|^4529 ≤ (19665820994347/50000000000000 : ℝ)^3505
        have hw : |(48570243/100000000 : ℝ)|=(48570243/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1135686041/5000000000 : ℝ)|^4529 ≤ (7365382281541/50000000000000 : ℝ)^3505
        have hw : |(-1135686041/5000000000 : ℝ)|=(1135686041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_s0_3 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2072033463/5000000000 : ℝ)*x 0 + (3091308967/10000000000 : ℝ)*x 1 + (1097039289/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2072033463/5000000000 : ℝ)^4529 ≤ (32037338747961/100000000000000 : ℝ)^3505 := by
    have hnat : (2072033463 : ℕ)^4529*100000000000000^3505 ≤ 32037338747961^3505*5000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072033463 5000000000 32037338747961 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3091308967/10000000000 : ℝ)^4529 ≤ (21937414790213/100000000000000 : ℝ)^3505 := by
    have hnat : (3091308967 : ℕ)^4529*100000000000000^3505 ≤ 21937414790213^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091308967 10000000000 21937414790213 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1097039289/2000000000 : ℝ)^4529 ≤ (1150631161083/2500000000000 : ℝ)^3505 := by
    have hnat : (1097039289 : ℕ)^4529*2500000000000^3505 ≤ 1150631161083^3505*2000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097039289 2000000000 1150631161083 2500000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2072033463/5000000000 : ℝ), (3091308967/10000000000 : ℝ), (1097039289/2000000000 : ℝ)] ![(32037338747961/100000000000000 : ℝ), (21937414790213/100000000000000 : ℝ), (1150631161083/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2072033463/5000000000 : ℝ)|^4529 ≤ (32037338747961/100000000000000 : ℝ)^3505
        have hw : |(2072033463/5000000000 : ℝ)|=(2072033463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3091308967/10000000000 : ℝ)|^4529 ≤ (21937414790213/100000000000000 : ℝ)^3505
        have hw : |(3091308967/10000000000 : ℝ)|=(3091308967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1097039289/2000000000 : ℝ)|^4529 ≤ (1150631161083/2500000000000 : ℝ)^3505
        have hw : |(1097039289/2000000000 : ℝ)|=(1097039289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_s0_4 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1685086213/10000000000 : ℝ)*x 0 + (488385617/1000000000 : ℝ)*x 1 + (2940981477/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1685086213/10000000000 : ℝ)^4529 ≤ (10015592238949/100000000000000 : ℝ)^3505 := by
    have hnat : (1685086213 : ℕ)^4529*100000000000000^3505 ≤ 10015592238949^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1685086213 10000000000 10015592238949 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (488385617/1000000000 : ℝ)^4529 ≤ (39612629430723/100000000000000 : ℝ)^3505 := by
    have hnat : (488385617 : ℕ)^4529*100000000000000^3505 ≤ 39612629430723^3505*1000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      488385617 1000000000 39612629430723 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2940981477/5000000000 : ℝ)^4529 ≤ (12592944579133/25000000000000 : ℝ)^3505 := by
    have hnat : (2940981477 : ℕ)^4529*25000000000000^3505 ≤ 12592944579133^3505*5000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2940981477 5000000000 12592944579133 25000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1685086213/10000000000 : ℝ), (488385617/1000000000 : ℝ), (2940981477/5000000000 : ℝ)] ![(10015592238949/100000000000000 : ℝ), (39612629430723/100000000000000 : ℝ), (12592944579133/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1685086213/10000000000 : ℝ)|^4529 ≤ (10015592238949/100000000000000 : ℝ)^3505
        have hw : |(-1685086213/10000000000 : ℝ)|=(1685086213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(488385617/1000000000 : ℝ)|^4529 ≤ (39612629430723/100000000000000 : ℝ)^3505
        have hw : |(488385617/1000000000 : ℝ)|=(488385617/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2940981477/5000000000 : ℝ)|^4529 ≤ (12592944579133/25000000000000 : ℝ)^3505
        have hw : |(2940981477/5000000000 : ℝ)|=(2940981477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_s0_5 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5189474467/10000000000 : ℝ)*x 0 + (-1246433627/10000000000 : ℝ)*x 1 + (5881962999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5189474467/10000000000 : ℝ)^4529 ≤ (1338891974347/3125000000000 : ℝ)^3505 := by
    have hnat : (5189474467 : ℕ)^4529*3125000000000^3505 ≤ 1338891974347^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5189474467 10000000000 1338891974347 3125000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1246433627/10000000000 : ℝ)^4529 ≤ (6783677993533/100000000000000 : ℝ)^3505 := by
    have hnat : (1246433627 : ℕ)^4529*100000000000000^3505 ≤ 6783677993533^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1246433627 10000000000 6783677993533 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5881962999/10000000000 : ℝ)^4529 ≤ (50371778814489/100000000000000 : ℝ)^3505 := by
    have hnat : (5881962999 : ℕ)^4529*100000000000000^3505 ≤ 50371778814489^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5881962999 10000000000 50371778814489 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5189474467/10000000000 : ℝ), (-1246433627/10000000000 : ℝ), (5881962999/10000000000 : ℝ)] ![(1338891974347/3125000000000 : ℝ), (6783677993533/100000000000000 : ℝ), (50371778814489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5189474467/10000000000 : ℝ)|^4529 ≤ (1338891974347/3125000000000 : ℝ)^3505
        have hw : |(5189474467/10000000000 : ℝ)|=(5189474467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1246433627/10000000000 : ℝ)|^4529 ≤ (6783677993533/100000000000000 : ℝ)^3505
        have hw : |(-1246433627/10000000000 : ℝ)|=(1246433627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5881962999/10000000000 : ℝ)|^4529 ≤ (50371778814489/100000000000000 : ℝ)^3505
        have hw : |(5881962999/10000000000 : ℝ)|=(5881962999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_s0_6 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5189474433/10000000000 : ℝ)*x 0 + (588196311/1000000000 : ℝ)*x 1 + (-38951047/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5189474433/10000000000 : ℝ)^4529 ≤ (4284454281639/10000000000000 : ℝ)^3505 := by
    have hnat : (5189474433 : ℕ)^4529*10000000000000^3505 ≤ 4284454281639^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5189474433 10000000000 4284454281639 10000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (588196311/1000000000 : ℝ)^4529 ≤ (50371780042783/100000000000000 : ℝ)^3505 := by
    have hnat : (588196311 : ℕ)^4529*100000000000000^3505 ≤ 50371780042783^3505*1000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      588196311 1000000000 50371780042783 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (38951047/312500000 : ℝ)^4529 ≤ (1356735425707/20000000000000 : ℝ)^3505 := by
    have hnat : (38951047 : ℕ)^4529*20000000000000^3505 ≤ 1356735425707^3505*312500000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38951047 312500000 1356735425707 20000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5189474433/10000000000 : ℝ), (588196311/1000000000 : ℝ), (-38951047/312500000 : ℝ)] ![(4284454281639/10000000000000 : ℝ), (50371780042783/100000000000000 : ℝ), (1356735425707/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5189474433/10000000000 : ℝ)|^4529 ≤ (4284454281639/10000000000000 : ℝ)^3505
        have hw : |(5189474433/10000000000 : ℝ)|=(5189474433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(588196311/1000000000 : ℝ)|^4529 ≤ (50371780042783/100000000000000 : ℝ)^3505
        have hw : |(588196311/1000000000 : ℝ)|=(588196311/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-38951047/312500000 : ℝ)|^4529 ≤ (1356735425707/20000000000000 : ℝ)^3505
        have hw : |(-38951047/312500000 : ℝ)|=(38951047/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_s0_7 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4151994633/10000000000 : ℝ)*x 0 + (5424181389/10000000000 : ℝ)*x 1 + (315450837/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4151994633/10000000000 : ℝ)^4529 ≤ (32116554737807/100000000000000 : ℝ)^3505 := by
    have hnat : (4151994633 : ℕ)^4529*100000000000000^3505 ≤ 32116554737807^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4151994633 10000000000 32116554737807 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424181389/10000000000 : ℝ)^4529 ≤ (22682392760981/50000000000000 : ℝ)^3505 := by
    have hnat : (5424181389 : ℕ)^4529*50000000000000^3505 ≤ 22682392760981^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424181389 10000000000 22682392760981 50000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (315450837/1000000000 : ℝ)^4529 ≤ (11259329862451/50000000000000 : ℝ)^3505 := by
    have hnat : (315450837 : ℕ)^4529*50000000000000^3505 ≤ 11259329862451^3505*1000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315450837 1000000000 11259329862451 50000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4151994633/10000000000 : ℝ), (5424181389/10000000000 : ℝ), (315450837/1000000000 : ℝ)] ![(32116554737807/100000000000000 : ℝ), (22682392760981/50000000000000 : ℝ), (11259329862451/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4151994633/10000000000 : ℝ)|^4529 ≤ (32116554737807/100000000000000 : ℝ)^3505
        have hw : |(4151994633/10000000000 : ℝ)|=(4151994633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424181389/10000000000 : ℝ)|^4529 ≤ (22682392760981/50000000000000 : ℝ)^3505
        have hw : |(5424181389/10000000000 : ℝ)|=(5424181389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(315450837/1000000000 : ℝ)|^4529 ≤ (11259329862451/50000000000000 : ℝ)^3505
        have hw : |(315450837/1000000000 : ℝ)|=(315450837/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1516_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20462363/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2879/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3179/12500 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4527/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4527 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4527*1^1024 ≤ 0^1024*1^4527 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4527 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4527 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4527/1024 : ℝ) ≤ (348159005472082349/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4527 ≤ (348159005472082349/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4527*20000000000000000000^1024 ≤ 348159005472082349^1024*5^4527 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 348159005472082349 20000000000000000000 4527 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (348159005472082349/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4527 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4527/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4527 := by
      have hnat : (1 : ℕ)^1024*1^4527 ≤ 1^4527*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4527 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20348159005472082349/20000000000000000000 : ℝ) ≤ (1254889248688581/1250000000000000 : ℝ) ^ (4527/1024 : ℝ) := by
    have hpowers : (20348159005472082349/20000000000000000000 : ℝ)^1024 ≤ (1254889248688581/1250000000000000 : ℝ)^4527 := by
      have hnat : (20348159005472082349 : ℕ)^1024*1250000000000000^4527 ≤ 1254889248688581^4527*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20348159005472082349 20000000000000000000 1254889248688581 1250000000000000 1024 4527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1254889248688581/1250000000000000 : ℝ)) (X := (20348159005472082349/20000000000000000000 : ℝ)) (by norm_num) 4527 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10348159005472082349/10000000000000000000 : ℝ) ≤ (629889248688581/625000000000000 : ℝ) ^ (4527/1024 : ℝ) := by
    have hpowers : (10348159005472082349/10000000000000000000 : ℝ)^1024 ≤ (629889248688581/625000000000000 : ℝ)^4527 := by
      have hnat : (10348159005472082349 : ℕ)^1024*625000000000000^4527 ≤ 629889248688581^4527*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10348159005472082349 10000000000000000000 629889248688581 625000000000000 1024 4527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (629889248688581/625000000000000 : ℝ)) (X := (10348159005472082349/10000000000000000000 : ℝ)) (by norm_num) 4527 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(4889248688581/500000000000000 : ℝ)*(0 : ℝ))^(4527/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(4889248688581/500000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(348159005472082349/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(4889248688581/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4527/1024 : ℝ) := by
    rw [show (1 : ℝ)+(4889248688581/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1254889248688581/1250000000000000 : ℝ) by norm_num, show 1+(348159005472082349/20000000000000000000 : ℝ)+(0 : ℝ)=(20348159005472082349/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(348159005472082349/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(4889248688581/500000000000000 : ℝ)*(2/5 : ℝ))^(4527/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(4889248688581/500000000000000 : ℝ)*(2/5 : ℝ)=(629889248688581/625000000000000 : ℝ) by norm_num, show 1+2*(348159005472082349/20000000000000000000 : ℝ)=(10348159005472082349/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(4889248688581/500000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4527/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4889248688581/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(4889248688581/500000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4527/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4889248688581/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(4889248688581/500000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4527/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4889248688581/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1681599913/10000000000 : ℝ)*X 0 0+(5909755289/10000000000 : ℝ)*X 0 1+(121425609/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((342319387/625000000 : ℝ)*X 1 0+(-2271372261/10000000000 : ℝ)*X 1 1+(18972751/39062500 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((342319393/625000000 : ℝ)*X 2 0+(48570243/100000000 : ℝ)*X 2 1+(-1135686041/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2072033463/5000000000 : ℝ)*X 0 0+(3091308967/10000000000 : ℝ)*X 0 1+(1097039289/2000000000 : ℝ)*X 0 2+(2072033463/5000000000 : ℝ)*X 1 0+(3091308967/10000000000 : ℝ)*X 1 1+(1097039289/2000000000 : ℝ)*X 1 2+(2072033463/5000000000 : ℝ)*X 2 0+(3091308967/10000000000 : ℝ)*X 2 1+(1097039289/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1685086213/10000000000 : ℝ)*X 0 0+(488385617/1000000000 : ℝ)*X 0 1+(2940981477/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5189474467/10000000000 : ℝ)*X 1 0+(-1246433627/10000000000 : ℝ)*X 1 1+(5881962999/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5189474433/10000000000 : ℝ)*X 2 0+(588196311/1000000000 : ℝ)*X 2 1+(-38951047/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4151994633/10000000000 : ℝ)*X 0 0+(5424181389/10000000000 : ℝ)*X 0 1+(315450837/1000000000 : ℝ)*X 0 2+(4151994633/10000000000 : ℝ)*X 1 0+(5424181389/10000000000 : ℝ)*X 1 1+(315450837/1000000000 : ℝ)*X 1 2+(4151994633/10000000000 : ℝ)*X 2 0+(5424181389/10000000000 : ℝ)*X 2 1+(315450837/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3370459818457381203/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12471673/100000000000000 : ℝ)*(base1) + (167321833/20000000000000 : ℝ)*(base19) + (426629399/50000000000000 : ℝ)*(base23) + (41128713/50000000000000 : ℝ)*(upper3) + (138136977/100000000000000 : ℝ)*(upper5) + (683824818910203/100000000000000 : ℝ)*(major0) + (683824818910203/100000000000000 : ℝ)*(major1) + (683824818910203/100000000000000 : ℝ)*(major2) + (189982601416731/20000000000000 : ℝ)*(sp0) + (47495769896181/5000000000000 : ℝ)*(sp1) + (949915381273987/100000000000000 : ℝ)*(sp2) + (417731967553963/100000000000000 : ℝ)*(sp3) + (3239920803/100000000000000 : ℝ)*(sp4) + (32772833/2500000000000 : ℝ)*(sp7) + (104433322734739/25000000000000 : ℝ)*(f.failure) + (189983246906557/20000000000000 : ℝ)*(f.sum) + (20381644391943/25000000000000000000000000000 : ℝ)*base65 + (26872675191943/50000000000000000000000000000 : ℝ)*base67 + (25698539358057/50000000000000000000000000000 : ℝ)*base70 + (5013633591943/50000000000000000000000000000 : ℝ)*base71 + (8917221533057/25000000000000000000000000000 : ℝ)*base74 + (142826482258057/50000000000000000000000000000 : ℝ)*base76 + (95233527208057/50000000000000000000000000000 : ℝ)*base78 + (31741239558057/50000000000000000000000000000 : ℝ)*base80 + (4499375466943/25000000000000000000000000000 : ℝ)*base81 + (2246743/312500000000000000000 : ℝ)*base90 + (2246743/312500000000000000000 : ℝ)*base92 + (2246743/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26031164506511565976989/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (470561883/100000000000000 : ℝ)*(base19) + (97433487/20000000000000 : ℝ)*(base23) + (18154819/100000000000000 : ℝ)*(base39) + (68461281/100000000000000 : ℝ)*(upper3) + (72834447/100000000000000 : ℝ)*(upper5) + (721244420766173/100000000000000 : ℝ)*(major0) + (721244420766173/100000000000000 : ℝ)*(major1) + (360622201305677/50000000000000 : ℝ)*(major2) + (633337257/50000000000000 : ℝ)*(sp1) + (170415429/12500000000000 : ℝ)*(sp2) + (250474166246003/25000000000000 : ℝ)*(sp4) + (500947463873807/50000000000000 : ℝ)*(sp5) + (500947416323981/50000000000000 : ℝ)*(sp6) + (440592088977073/100000000000000 : ℝ)*(sp7) + (440592088977073/100000000000000 : ℝ)*(f.failure) + (100189668313883/10000000000000 : ℝ)*(f.sum) + (29851315730813/50000000000000000000000000000 : ℝ)*base66 + (40361949449337/25000000000000000000000000000 : ℝ)*base67 + (180841126729487/50000000000000000000000000000 : ℝ)*base70 + (4526469499337/25000000000000000000000000000 : ℝ)*base71 + (66598703669187/50000000000000000000000000000 : ℝ)*base73 + (52796147170513/50000000000000000000000000000 : ℝ)*base75 + (208139837620513/50000000000000000000000000000 : ℝ)*base77 + (299384805320513/50000000000000000000000000000 : ℝ)*base79 + (37227922279487/25000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base88 + (3903499/1250000000000000000000 : ℝ)*base89 + (3903499/1250000000000000000000 : ℝ)*base91 + (3903499/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1516_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20462363/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2879/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3179/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1516_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1516_s1_0 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-917122039/5000000000 : ℝ)*x 0 + (55678579/100000000 : ℝ)*x 1 + (5100796967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (917122039/5000000000 : ℝ)^4529 ≤ (5587829352571/50000000000000 : ℝ)^3505 := by
    have hnat : (917122039 : ℕ)^4529*50000000000000^3505 ≤ 5587829352571^3505*5000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      917122039 5000000000 5587829352571 50000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (55678579/100000000 : ℝ)^4529 ≤ (46923446135283/100000000000000 : ℝ)^3505 := by
    have hnat : (55678579 : ℕ)^4529*100000000000000^3505 ≤ 46923446135283^3505*100000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55678579 100000000 46923446135283 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5100796967/10000000000 : ℝ)^4529 ≤ (20950447572277/50000000000000 : ℝ)^3505 := by
    have hnat : (5100796967 : ℕ)^4529*50000000000000^3505 ≤ 20950447572277^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5100796967 10000000000 20950447572277 50000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-917122039/5000000000 : ℝ), (55678579/100000000 : ℝ), (5100796967/10000000000 : ℝ)] ![(5587829352571/50000000000000 : ℝ), (46923446135283/100000000000000 : ℝ), (20950447572277/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-917122039/5000000000 : ℝ)|^4529 ≤ (5587829352571/50000000000000 : ℝ)^3505
        have hw : |(-917122039/5000000000 : ℝ)|=(917122039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(55678579/100000000 : ℝ)|^4529 ≤ (46923446135283/100000000000000 : ℝ)^3505
        have hw : |(55678579/100000000 : ℝ)|=(55678579/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5100796967/10000000000 : ℝ)|^4529 ≤ (20950447572277/50000000000000 : ℝ)^3505
        have hw : |(5100796967/10000000000 : ℝ)|=(5100796967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_s1_1 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5385893467/10000000000 : ℝ)*x 0 + (-2080059379/10000000000 : ℝ)*x 1 + (5100796393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5385893467/10000000000 : ℝ)^4529 ≤ (8990288242577/20000000000000 : ℝ)^3505 := by
    have hnat : (5385893467 : ℕ)^4529*20000000000000^3505 ≤ 8990288242577^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385893467 10000000000 8990288242577 20000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2080059379/10000000000 : ℝ)^4529 ≤ (13147669721051/100000000000000 : ℝ)^3505 := by
    have hnat : (2080059379 : ℕ)^4529*100000000000000^3505 ≤ 13147669721051^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080059379 10000000000 13147669721051 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5100796393/10000000000 : ℝ)^4529 ≤ (4190088905183/10000000000000 : ℝ)^3505 := by
    have hnat : (5100796393 : ℕ)^4529*10000000000000^3505 ≤ 4190088905183^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5100796393 10000000000 4190088905183 10000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5385893467/10000000000 : ℝ), (-2080059379/10000000000 : ℝ), (5100796393/10000000000 : ℝ)] ![(8990288242577/20000000000000 : ℝ), (13147669721051/100000000000000 : ℝ), (4190088905183/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5385893467/10000000000 : ℝ)|^4529 ≤ (8990288242577/20000000000000 : ℝ)^3505
        have hw : |(5385893467/10000000000 : ℝ)|=(5385893467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2080059379/10000000000 : ℝ)|^4529 ≤ (13147669721051/100000000000000 : ℝ)^3505
        have hw : |(-2080059379/10000000000 : ℝ)|=(2080059379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5100796393/10000000000 : ℝ)|^4529 ≤ (4190088905183/10000000000000 : ℝ)^3505
        have hw : |(5100796393/10000000000 : ℝ)|=(5100796393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_s1_2 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2692946469/5000000000 : ℝ)*x 0 + (1275199241/2500000000 : ℝ)*x 1 + (-416011867/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2692946469/5000000000 : ℝ)^4529 ≤ (44951435507883/100000000000000 : ℝ)^3505 := by
    have hnat : (2692946469 : ℕ)^4529*100000000000000^3505 ≤ 44951435507883^3505*5000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692946469 5000000000 44951435507883 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1275199241/2500000000 : ℝ)^4529 ≤ (4190089511271/10000000000000 : ℝ)^3505 := by
    have hnat : (1275199241 : ℕ)^4529*10000000000000^3505 ≤ 4190089511271^3505*2500000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1275199241 2500000000 4190089511271 10000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (416011867/2000000000 : ℝ)^4529 ≤ (13147669361683/100000000000000 : ℝ)^3505 := by
    have hnat : (416011867 : ℕ)^4529*100000000000000^3505 ≤ 13147669361683^3505*2000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416011867 2000000000 13147669361683 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2692946469/5000000000 : ℝ), (1275199241/2500000000 : ℝ), (-416011867/2000000000 : ℝ)] ![(44951435507883/100000000000000 : ℝ), (4190089511271/10000000000000 : ℝ), (13147669361683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2692946469/5000000000 : ℝ)|^4529 ≤ (44951435507883/100000000000000 : ℝ)^3505
        have hw : |(2692946469/5000000000 : ℝ)|=(2692946469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1275199241/2500000000 : ℝ)|^4529 ≤ (4190089511271/10000000000000 : ℝ)^3505
        have hw : |(1275199241/2500000000 : ℝ)|=(1275199241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-416011867/2000000000 : ℝ)|^4529 ≤ (13147669361683/100000000000000 : ℝ)^3505
        have hw : |(-416011867/2000000000 : ℝ)|=(416011867/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_s1_3 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2124077021/5000000000 : ℝ)*x 0 + (3745046141/10000000000 : ℝ)*x 1 + (4807132887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2124077021/5000000000 : ℝ)^4529 ≤ (33080910137209/100000000000000 : ℝ)^3505 := by
    have hnat : (2124077021 : ℕ)^4529*100000000000000^3505 ≤ 33080910137209^3505*5000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124077021 5000000000 33080910137209 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3745046141/10000000000 : ℝ)^4529 ≤ (7027178095569/25000000000000 : ℝ)^3505 := by
    have hnat : (3745046141 : ℕ)^4529*25000000000000^3505 ≤ 7027178095569^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3745046141 10000000000 7027178095569 25000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4807132887/10000000000 : ℝ)^4529 ≤ (38810377470277/100000000000000 : ℝ)^3505 := by
    have hnat : (4807132887 : ℕ)^4529*100000000000000^3505 ≤ 38810377470277^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4807132887 10000000000 38810377470277 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2124077021/5000000000 : ℝ), (3745046141/10000000000 : ℝ), (4807132887/10000000000 : ℝ)] ![(33080910137209/100000000000000 : ℝ), (7027178095569/25000000000000 : ℝ), (38810377470277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2124077021/5000000000 : ℝ)|^4529 ≤ (33080910137209/100000000000000 : ℝ)^3505
        have hw : |(2124077021/5000000000 : ℝ)|=(2124077021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3745046141/10000000000 : ℝ)|^4529 ≤ (7027178095569/25000000000000 : ℝ)^3505
        have hw : |(3745046141/10000000000 : ℝ)|=(3745046141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4807132887/10000000000 : ℝ)|^4529 ≤ (38810377470277/100000000000000 : ℝ)^3505
        have hw : |(4807132887/10000000000 : ℝ)|=(4807132887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_s1_4 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-183453857/1000000000 : ℝ)*x 0 + (1276497673/2500000000 : ℝ)*x 1 + (1390645259/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (183453857/1000000000 : ℝ)^4529 ≤ (11177977241921/100000000000000 : ℝ)^3505 := by
    have hnat : (183453857 : ℕ)^4529*100000000000000^3505 ≤ 11177977241921^3505*1000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183453857 1000000000 11177977241921 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1276497673/2500000000 : ℝ)^4529 ≤ (41956032139017/100000000000000 : ℝ)^3505 := by
    have hnat : (1276497673 : ℕ)^4529*100000000000000^3505 ≤ 41956032139017^3505*2500000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1276497673 2500000000 41956032139017 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1390645259/2500000000 : ℝ)^4529 ≤ (11716497652013/25000000000000 : ℝ)^3505 := by
    have hnat : (1390645259 : ℕ)^4529*25000000000000^3505 ≤ 11716497652013^3505*2500000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1390645259 2500000000 11716497652013 25000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-183453857/1000000000 : ℝ), (1276497673/2500000000 : ℝ), (1390645259/2500000000 : ℝ)] ![(11177977241921/100000000000000 : ℝ), (41956032139017/100000000000000 : ℝ), (11716497652013/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-183453857/1000000000 : ℝ)|^4529 ≤ (11177977241921/100000000000000 : ℝ)^3505
        have hw : |(-183453857/1000000000 : ℝ)|=(183453857/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1276497673/2500000000 : ℝ)|^4529 ≤ (41956032139017/100000000000000 : ℝ)^3505
        have hw : |(1276497673/2500000000 : ℝ)|=(1276497673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1390645259/2500000000 : ℝ)|^4529 ≤ (11716497652013/25000000000000 : ℝ)^3505
        have hw : |(1390645259/2500000000 : ℝ)|=(1390645259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_s1_5 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1315703303/2500000000 : ℝ)*x 0 + (-404568681/2500000000 : ℝ)*x 1 + (1112516231/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1315703303/2500000000 : ℝ)^4529 ≤ (21814268440167/50000000000000 : ℝ)^3505 := by
    have hnat : (1315703303 : ℕ)^4529*50000000000000^3505 ≤ 21814268440167^3505*2500000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315703303 2500000000 21814268440167 50000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (404568681/2500000000 : ℝ)^4529 ≤ (37130746871/390625000000 : ℝ)^3505 := by
    have hnat : (404568681 : ℕ)^4529*390625000000^3505 ≤ 37130746871^3505*2500000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404568681 2500000000 37130746871 390625000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1112516231/2000000000 : ℝ)^4529 ≤ (2929124493973/6250000000000 : ℝ)^3505 := by
    have hnat : (1112516231 : ℕ)^4529*6250000000000^3505 ≤ 2929124493973^3505*2000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1112516231 2000000000 2929124493973 6250000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1315703303/2500000000 : ℝ), (-404568681/2500000000 : ℝ), (1112516231/2000000000 : ℝ)] ![(21814268440167/50000000000000 : ℝ), (37130746871/390625000000 : ℝ), (2929124493973/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1315703303/2500000000 : ℝ)|^4529 ≤ (21814268440167/50000000000000 : ℝ)^3505
        have hw : |(1315703303/2500000000 : ℝ)|=(1315703303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-404568681/2500000000 : ℝ)|^4529 ≤ (37130746871/390625000000 : ℝ)^3505
        have hw : |(-404568681/2500000000 : ℝ)|=(404568681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1112516231/2000000000 : ℝ)|^4529 ≤ (2929124493973/6250000000000 : ℝ)^3505
        have hw : |(1112516231/2000000000 : ℝ)|=(1112516231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_s1_6 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5262812981/10000000000 : ℝ)*x 0 + (1390645319/2500000000 : ℝ)*x 1 + (-1618274877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5262812981/10000000000 : ℝ)^4529 ≤ (21814267202941/50000000000000 : ℝ)^3505 := by
    have hnat : (5262812981 : ℕ)^4529*50000000000000^3505 ≤ 21814267202941^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262812981 10000000000 21814267202941 50000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1390645319/2500000000 : ℝ)^4529 ≤ (46865993220857/100000000000000 : ℝ)^3505 := by
    have hnat : (1390645319 : ℕ)^4529*100000000000000^3505 ≤ 46865993220857^3505*2500000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1390645319 2500000000 46865993220857 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1618274877/10000000000 : ℝ)^4529 ≤ (950547236023/10000000000000 : ℝ)^3505 := by
    have hnat : (1618274877 : ℕ)^4529*10000000000000^3505 ≤ 950547236023^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1618274877 10000000000 950547236023 10000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5262812981/10000000000 : ℝ), (1390645319/2500000000 : ℝ), (-1618274877/10000000000 : ℝ)] ![(21814267202941/50000000000000 : ℝ), (46865993220857/100000000000000 : ℝ), (950547236023/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5262812981/10000000000 : ℝ)|^4529 ≤ (21814267202941/50000000000000 : ℝ)^3505
        have hw : |(5262812981/10000000000 : ℝ)|=(5262812981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1390645319/2500000000 : ℝ)|^4529 ≤ (46865993220857/100000000000000 : ℝ)^3505
        have hw : |(1390645319/2500000000 : ℝ)|=(1390645319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1618274877/10000000000 : ℝ)|^4529 ≤ (950547236023/10000000000000 : ℝ)^3505
        have hw : |(-1618274877/10000000000 : ℝ)|=(1618274877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_s1_7 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (849764771/2000000000 : ℝ)*x 0 + (1198830609/2500000000 : ℝ)*x 1 + (3757045127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (849764771/2000000000 : ℝ)^4529 ≤ (6617530012449/20000000000000 : ℝ)^3505 := by
    have hnat : (849764771 : ℕ)^4529*20000000000000^3505 ≤ 6617530012449^3505*2000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849764771 2000000000 6617530012449 20000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1198830609/2500000000 : ℝ)^4529 ≤ (38687212689927/100000000000000 : ℝ)^3505 := by
    have hnat : (1198830609 : ℕ)^4529*100000000000000^3505 ≤ 38687212689927^3505*2500000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1198830609 2500000000 38687212689927 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3757045127/10000000000 : ℝ)^4529 ≤ (28225137231383/100000000000000 : ℝ)^3505 := by
    have hnat : (3757045127 : ℕ)^4529*100000000000000^3505 ≤ 28225137231383^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3757045127 10000000000 28225137231383 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(849764771/2000000000 : ℝ), (1198830609/2500000000 : ℝ), (3757045127/10000000000 : ℝ)] ![(6617530012449/20000000000000 : ℝ), (38687212689927/100000000000000 : ℝ), (28225137231383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(849764771/2000000000 : ℝ)|^4529 ≤ (6617530012449/20000000000000 : ℝ)^3505
        have hw : |(849764771/2000000000 : ℝ)|=(849764771/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1198830609/2500000000 : ℝ)|^4529 ≤ (38687212689927/100000000000000 : ℝ)^3505
        have hw : |(1198830609/2500000000 : ℝ)|=(1198830609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3757045127/10000000000 : ℝ)|^4529 ≤ (28225137231383/100000000000000 : ℝ)^3505
        have hw : |(3757045127/10000000000 : ℝ)|=(3757045127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1516_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20462363/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3179/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2879/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (841/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18289/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3179/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2879/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3179/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2879/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3179/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2879/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3179/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2879/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3179/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2879/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3179/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2879/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2879/100000 : ℝ) ^ (4527/1024 : ℝ) ≤ (7716740359121/50000000000000000000 : ℝ) := by
    have hpowers : (2879/100000 : ℝ)^4527 ≤ (7716740359121/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2879 : ℕ)^4527*50000000000000000000^1024 ≤ 7716740359121^1024*100000^4527 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2879 100000 7716740359121 50000000000000000000 4527 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2879/100000 : ℝ)) (X := (7716740359121/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4527 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3179/12500 : ℝ) ^ (4527/1024 : ℝ) ≤ (117548651621757731/50000000000000000000 : ℝ) := by
    have hpowers : (3179/12500 : ℝ)^4527 ≤ (117548651621757731/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3179 : ℕ)^4527*50000000000000000000^1024 ≤ 117548651621757731^1024*12500^4527 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3179 12500 117548651621757731 50000000000000000000 4527 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3179/12500 : ℝ)) (X := (117548651621757731/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4527 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000007716740359121/25000000000000000000 : ℝ) ≤ (10000000698205539/10000000000000000 : ℝ) ^ (4527/1024 : ℝ) := by
    have hpowers : (25000007716740359121/25000000000000000000 : ℝ)^1024 ≤ (10000000698205539/10000000000000000 : ℝ)^4527 := by
      have hnat : (25000007716740359121 : ℕ)^1024*10000000000000000^4527 ≤ 10000000698205539^4527*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000007716740359121 25000000000000000000 10000000698205539 10000000000000000 1024 4527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000698205539/10000000000000000 : ℝ)) (X := (25000007716740359121/25000000000000000000 : ℝ)) (by norm_num) 4527 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12529389092090529213/12500000000000000000 : ℝ) ≤ (400212535226351/400000000000000 : ℝ) ^ (4527/1024 : ℝ) := by
    have hpowers : (12529389092090529213/12500000000000000000 : ℝ)^1024 ≤ (400212535226351/400000000000000 : ℝ)^4527 := by
      have hnat : (12529389092090529213 : ℕ)^1024*400000000000000^4527 ≤ 400212535226351^4527*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12529389092090529213 12500000000000000000 400212535226351 400000000000000 1024 4527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400212535226351/400000000000000 : ℝ)) (X := (12529389092090529213/12500000000000000000 : ℝ)) (by norm_num) 4527 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25117548651621757731/25000000000000000000 : ℝ) ≤ (10010626063112011/10000000000000000 : ℝ) ^ (4527/1024 : ℝ) := by
    have hpowers : (25117548651621757731/25000000000000000000 : ℝ)^1024 ≤ (10010626063112011/10000000000000000 : ℝ)^4527 := by
      have hnat : (25117548651621757731 : ℕ)^1024*10000000000000000^4527 ≤ 10010626063112011^4527*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25117548651621757731 25000000000000000000 10010626063112011 10000000000000000 1024 4527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10010626063112011/10000000000000000 : ℝ)) (X := (25117548651621757731/25000000000000000000 : ℝ)) (by norm_num) 4527 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7716740359121/50000000000000000000 : ℝ) ≤ ((225499425321063788179/225530000000000000000 : ℝ)+2*(1328170613309/563825000000000 : ℝ)*(2879/100000 : ℝ))^(4527/1024 : ℝ) := by
    rw [show (225499425321063788179/225530000000000000000 : ℝ)+2*(1328170613309/563825000000000 : ℝ)*(2879/100000 : ℝ)=(10000000698205539/10000000000000000 : ℝ) by norm_num, show 1+2*(7716740359121/50000000000000000000 : ℝ)=(25000007716740359121/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(117548651621757731/50000000000000000000 : ℝ)+(7716740359121/50000000000000000000 : ℝ) ≤ ((225499425321063788179/225530000000000000000 : ℝ)+(1328170613309/563825000000000 : ℝ)*((3179/12500 : ℝ)+(2879/100000 : ℝ)))^(4527/1024 : ℝ) := by
    rw [show (225499425321063788179/225530000000000000000 : ℝ)+(1328170613309/563825000000000 : ℝ)*((3179/12500 : ℝ)+(2879/100000 : ℝ))=(400212535226351/400000000000000 : ℝ) by norm_num, show 1+(117548651621757731/50000000000000000000 : ℝ)+(7716740359121/50000000000000000000 : ℝ)=(12529389092090529213/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(117548651621757731/50000000000000000000 : ℝ) ≤ ((225499425321063788179/225530000000000000000 : ℝ)+2*(1328170613309/563825000000000 : ℝ)*(3179/12500 : ℝ))^(4527/1024 : ℝ) := by
    rw [show (225499425321063788179/225530000000000000000 : ℝ)+2*(1328170613309/563825000000000 : ℝ)*(3179/12500 : ℝ)=(10010626063112011/10000000000000000 : ℝ) by norm_num, show 1+2*(117548651621757731/50000000000000000000 : ℝ)=(25117548651621757731/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (225499425321063788179/225530000000000000000 : ℝ)*(X 1 0+X 2 0)+(1328170613309/563825000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4527/1024 : ℝ)) (lo := (2879/100000 : ℝ)) (hi := (3179/12500 : ℝ)) (c := (225499425321063788179/225530000000000000000 : ℝ)) (alpha := (1328170613309/563825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (225499425321063788179/225530000000000000000 : ℝ)*(X 0 1+X 2 1)+(1328170613309/563825000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4527/1024 : ℝ)) (lo := (2879/100000 : ℝ)) (hi := (3179/12500 : ℝ)) (c := (225499425321063788179/225530000000000000000 : ℝ)) (alpha := (1328170613309/563825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (225499425321063788179/225530000000000000000 : ℝ)*(X 0 2+X 1 2)+(1328170613309/563825000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4527/1024 : ℝ)) (lo := (2879/100000 : ℝ)) (hi := (3179/12500 : ℝ)) (c := (225499425321063788179/225530000000000000000 : ℝ)) (alpha := (1328170613309/563825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-917122039/5000000000 : ℝ)*X 0 0+(55678579/100000000 : ℝ)*X 0 1+(5100796967/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5385893467/10000000000 : ℝ)*X 1 0+(-2080059379/10000000000 : ℝ)*X 1 1+(5100796393/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2692946469/5000000000 : ℝ)*X 2 0+(1275199241/2500000000 : ℝ)*X 2 1+(-416011867/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2124077021/5000000000 : ℝ)*X 0 0+(3745046141/10000000000 : ℝ)*X 0 1+(4807132887/10000000000 : ℝ)*X 0 2+(2124077021/5000000000 : ℝ)*X 1 0+(3745046141/10000000000 : ℝ)*X 1 1+(4807132887/10000000000 : ℝ)*X 1 2+(2124077021/5000000000 : ℝ)*X 2 0+(3745046141/10000000000 : ℝ)*X 2 1+(4807132887/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-183453857/1000000000 : ℝ)*X 0 0+(1276497673/2500000000 : ℝ)*X 0 1+(1390645259/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1315703303/2500000000 : ℝ)*X 1 0+(-404568681/2500000000 : ℝ)*X 1 1+(1112516231/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5262812981/10000000000 : ℝ)*X 2 0+(1390645319/2500000000 : ℝ)*X 2 1+(-1618274877/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((849764771/2000000000 : ℝ)*X 0 0+(1198830609/2500000000 : ℝ)*X 0 1+(3757045127/10000000000 : ℝ)*X 0 2+(849764771/2000000000 : ℝ)*X 1 0+(1198830609/2500000000 : ℝ)*X 1 1+(3757045127/10000000000 : ℝ)*X 1 2+(849764771/2000000000 : ℝ)*X 2 0+(1198830609/2500000000 : ℝ)*X 2 1+(3757045127/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32360096494059750595728840273/11276500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5991597/25000000000000 : ℝ)*(base1) + (531129663/100000000000000 : ℝ)*(base19) + (320836417/100000000000000 : ℝ)*(base23) + (27019541/100000000000000 : ℝ)*(upper3) + (6777039/100000000000000 : ℝ)*(upper5) + (1541299342195129/100000000000000 : ℝ)*(major0) + (1541299342195129/100000000000000 : ℝ)*(major1) + (1541299342195129/100000000000000 : ℝ)*(major2) + (42821023713043/2000000000000 : ℝ)*(sp0) + (214105275428609/10000000000000 : ℝ)*(sp1) + (428210592915867/20000000000000 : ℝ)*(sp2) + (470772015696579/50000000000000 : ℝ)*(sp3) + (212372999/10000000000000 : ℝ)*(sp4) + (249591701/20000000000000 : ℝ)*(sp7) + (470772651659027/50000000000000 : ℝ)*(f.failure) + (267631660676969/12500000000000 : ℝ)*(f.sum) + (545893243906029/112765000000000000000000000000 : ℝ)*base65 + (42614214977628019909/22553000000000000000000000000000000 : ℝ)*base68 + (158040244763922980091/22553000000000000000000000000000000 : ℝ)*base69 + (75500907177987019909/22553000000000000000000000000000000 : ℝ)*base72 + (20201125609389/7047812500000000000000000000 : ℝ)*base73 + (170479713994117019909/22553000000000000000000000000000000 : ℝ)*base76 + (11615418425412980091/22553000000000000000000000000000000 : ℝ)*base77 + (47449597573208019909/22553000000000000000000000000000000 : ℝ)*base80 + (178044110043151/28191250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (6450801/625000000000000000000 : ℝ)*base89 + (6450801/625000000000000000000 : ℝ)*base91 + (6450801/625000000000000000000 : ℝ)*base93 + (3/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15375568657573021009364895057/5638250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (591813231/100000000000000 : ℝ)*(base19) + (5533499/1000000000000 : ℝ)*(base23) + (10483587/12500000000000 : ℝ)*(upper3) + (6887371/25000000000000 : ℝ)*(lower4) + (2797851/20000000000000 : ℝ)*(upper5) + (1576639831474039/100000000000000 : ℝ)*(major0) + (1576639831474039/100000000000000 : ℝ)*(major1) + (1576639831474039/100000000000000 : ℝ)*(major2) + (4435104221/100000000000000 : ℝ)*(sp1) + (145707387/3125000000000 : ℝ)*(sp2) + (2190145554074049/100000000000000 : ℝ)*(sp4) + (1095070263578299/50000000000000 : ℝ)*(sp5) + (547535084521941/25000000000000 : ℝ)*(sp6) + (120391752246707/12500000000000 : ℝ)*(sp7) + (120391752246707/12500000000000 : ℝ)*(f.failure) + (2190145554074049/100000000000000 : ℝ)*(f.sum) + (103470459615773/56382500000000000000000000000 : ℝ)*base66 + (124111180588881984981/22553000000000000000000000000000000 : ℝ)*base67 + (208806465277825984981/22553000000000000000000000000000000 : ℝ)*base69 + (42565930074385015019/22553000000000000000000000000000000 : ℝ)*base72 + (338933656976879/112765000000000000000000000000 : ℝ)*base73 + (133987997859038984981/22553000000000000000000000000000000 : ℝ)*base75 + (226975715077385984981/22553000000000000000000000000000000 : ℝ)*base77 + (337428885982885984981/22553000000000000000000000000000000 : ℝ)*base79 + (10210627305057/14095625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (1748859/156250000000000000000 : ℝ)*base90 + (1748859/156250000000000000000 : ℝ)*base92 + (1748859/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1516_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20462363/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3179/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2879/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (841/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18289/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1516_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1516_s2_0 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-929152551/5000000000 : ℝ)*x 0 + (2728322153/5000000000 : ℝ)*x 1 + (1299104639/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (929152551/5000000000 : ℝ)^4529 ≤ (11365448671157/100000000000000 : ℝ)^3505 := by
    have hnat : (929152551 : ℕ)^4529*100000000000000^3505 ≤ 11365448671157^3505*5000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      929152551 5000000000 11365448671157 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2728322153/5000000000 : ℝ)^4529 ≤ (45715913534959/100000000000000 : ℝ)^3505 := by
    have hnat : (2728322153 : ℕ)^4529*100000000000000^3505 ≤ 45715913534959^3505*5000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728322153 5000000000 45715913534959 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1299104639/2500000000 : ℝ)^4529 ≤ (21459318890517/50000000000000 : ℝ)^3505 := by
    have hnat : (1299104639 : ℕ)^4529*50000000000000^3505 ≤ 21459318890517^3505*2500000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299104639 2500000000 21459318890517 50000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-929152551/5000000000 : ℝ), (2728322153/5000000000 : ℝ), (1299104639/2500000000 : ℝ)] ![(11365448671157/100000000000000 : ℝ), (45715913534959/100000000000000 : ℝ), (21459318890517/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-929152551/5000000000 : ℝ)|^4529 ≤ (11365448671157/100000000000000 : ℝ)^3505
        have hw : |(-929152551/5000000000 : ℝ)|=(929152551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2728322153/5000000000 : ℝ)|^4529 ≤ (45715913534959/100000000000000 : ℝ)^3505
        have hw : |(2728322153/5000000000 : ℝ)|=(2728322153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1299104639/2500000000 : ℝ)|^4529 ≤ (21459318890517/50000000000000 : ℝ)^3505
        have hw : |(1299104639/2500000000 : ℝ)|=(1299104639/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_s2_1 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5357599573/10000000000 : ℝ)*x 0 + (-498058107/2500000000 : ℝ)*x 1 + (2598209599/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5357599573/10000000000 : ℝ)^4529 ≤ (44646540060321/100000000000000 : ℝ)^3505 := by
    have hnat : (5357599573 : ℕ)^4529*100000000000000^3505 ≤ 44646540060321^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5357599573 10000000000 44646540060321 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (498058107/2500000000 : ℝ)^4529 ≤ (2486963059243/20000000000000 : ℝ)^3505 := by
    have hnat : (498058107 : ℕ)^4529*20000000000000^3505 ≤ 2486963059243^3505*2500000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      498058107 2500000000 2486963059243 20000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2598209599/5000000000 : ℝ)^4529 ≤ (2145932231631/5000000000000 : ℝ)^3505 := by
    have hnat : (2598209599 : ℕ)^4529*5000000000000^3505 ≤ 2145932231631^3505*5000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598209599 5000000000 2145932231631 5000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5357599573/10000000000 : ℝ), (-498058107/2500000000 : ℝ), (2598209599/5000000000 : ℝ)] ![(44646540060321/100000000000000 : ℝ), (2486963059243/20000000000000 : ℝ), (2145932231631/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5357599573/10000000000 : ℝ)|^4529 ≤ (44646540060321/100000000000000 : ℝ)^3505
        have hw : |(5357599573/10000000000 : ℝ)|=(5357599573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-498058107/2500000000 : ℝ)|^4529 ≤ (2486963059243/20000000000000 : ℝ)^3505
        have hw : |(-498058107/2500000000 : ℝ)|=(498058107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2598209599/5000000000 : ℝ)|^4529 ≤ (2145932231631/5000000000000 : ℝ)^3505
        have hw : |(2598209599/5000000000 : ℝ)|=(2598209599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_s2_2 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5357600409/10000000000 : ℝ)*x 0 + (5196418667/10000000000 : ℝ)*x 1 + (-398446403/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5357600409/10000000000 : ℝ)^4529 ≤ (44646549062303/100000000000000 : ℝ)^3505 := by
    have hnat : (5357600409 : ℕ)^4529*100000000000000^3505 ≤ 44646549062303^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5357600409 10000000000 44646549062303 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5196418667/10000000000 : ℝ)^4529 ≤ (21459319482827/50000000000000 : ℝ)^3505 := by
    have hnat : (5196418667 : ℕ)^4529*50000000000000^3505 ≤ 21459319482827^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196418667 10000000000 21459319482827 50000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (398446403/2000000000 : ℝ)^4529 ≤ (12434811965299/100000000000000 : ℝ)^3505 := by
    have hnat : (398446403 : ℕ)^4529*100000000000000^3505 ≤ 12434811965299^3505*2000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398446403 2000000000 12434811965299 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5357600409/10000000000 : ℝ), (5196418667/10000000000 : ℝ), (-398446403/2000000000 : ℝ)] ![(44646549062303/100000000000000 : ℝ), (21459319482827/50000000000000 : ℝ), (12434811965299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5357600409/10000000000 : ℝ)|^4529 ≤ (44646549062303/100000000000000 : ℝ)^3505
        have hw : |(5357600409/10000000000 : ℝ)|=(5357600409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5196418667/10000000000 : ℝ)|^4529 ≤ (21459319482827/50000000000000 : ℝ)^3505
        have hw : |(5196418667/10000000000 : ℝ)|=(5196418667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-398446403/2000000000 : ℝ)|^4529 ≤ (12434811965299/100000000000000 : ℝ)^3505
        have hw : |(-398446403/2000000000 : ℝ)|=(398446403/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_s2_3 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4265438721/10000000000 : ℝ)*x 0 + (795647979/2000000000 : ℝ)*x 1 + (4569988659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4265438721/10000000000 : ℝ)^4529 ≤ (33254934723357/100000000000000 : ℝ)^3505 := by
    have hnat : (4265438721 : ℕ)^4529*100000000000000^3505 ≤ 33254934723357^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4265438721 10000000000 33254934723357 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (795647979/2000000000 : ℝ)^4529 ≤ (30390584799967/100000000000000 : ℝ)^3505 := by
    have hnat : (795647979 : ℕ)^4529*100000000000000^3505 ≤ 30390584799967^3505*2000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      795647979 2000000000 30390584799967 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4569988659/10000000000 : ℝ)^4529 ≤ (7270896093657/20000000000000 : ℝ)^3505 := by
    have hnat : (4569988659 : ℕ)^4529*20000000000000^3505 ≤ 7270896093657^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4569988659 10000000000 7270896093657 20000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4265438721/10000000000 : ℝ), (795647979/2000000000 : ℝ), (4569988659/10000000000 : ℝ)] ![(33254934723357/100000000000000 : ℝ), (30390584799967/100000000000000 : ℝ), (7270896093657/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4265438721/10000000000 : ℝ)|^4529 ≤ (33254934723357/100000000000000 : ℝ)^3505
        have hw : |(4265438721/10000000000 : ℝ)|=(4265438721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(795647979/2000000000 : ℝ)|^4529 ≤ (30390584799967/100000000000000 : ℝ)^3505
        have hw : |(795647979/2000000000 : ℝ)|=(795647979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4569988659/10000000000 : ℝ)|^4529 ≤ (7270896093657/20000000000000 : ℝ)^3505
        have hw : |(4569988659/10000000000 : ℝ)|=(4569988659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_s2_4 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-929177499/5000000000 : ℝ)*x 0 + (649755057/1250000000 : ℝ)*x 1 + (2727504413/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (929177499/5000000000 : ℝ)^4529 ≤ (11365842993421/100000000000000 : ℝ)^3505 := by
    have hnat : (929177499 : ℕ)^4529*100000000000000^3505 ≤ 11365842993421^3505*5000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      929177499 5000000000 11365842993421 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (649755057/1250000000 : ℝ)^4529 ≤ (21467973948463/50000000000000 : ℝ)^3505 := by
    have hnat : (649755057 : ℕ)^4529*50000000000000^3505 ≤ 21467973948463^3505*1250000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649755057 1250000000 21467973948463 50000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2727504413/5000000000 : ℝ)^4529 ≤ (45698209091579/100000000000000 : ℝ)^3505 := by
    have hnat : (2727504413 : ℕ)^4529*100000000000000^3505 ≤ 45698209091579^3505*5000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2727504413 5000000000 45698209091579 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-929177499/5000000000 : ℝ), (649755057/1250000000 : ℝ), (2727504413/5000000000 : ℝ)] ![(11365842993421/100000000000000 : ℝ), (21467973948463/50000000000000 : ℝ), (45698209091579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-929177499/5000000000 : ℝ)|^4529 ≤ (11365842993421/100000000000000 : ℝ)^3505
        have hw : |(-929177499/5000000000 : ℝ)|=(929177499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(649755057/1250000000 : ℝ)|^4529 ≤ (21467973948463/50000000000000 : ℝ)^3505
        have hw : |(649755057/1250000000 : ℝ)|=(649755057/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2727504413/5000000000 : ℝ)|^4529 ≤ (45698209091579/100000000000000 : ℝ)^3505
        have hw : |(2727504413/5000000000 : ℝ)|=(2727504413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_s2_5 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644614571/5000000000 : ℝ)*x 0 + (-866821299/5000000000 : ℝ)*x 1 + (1091001963/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644614571/5000000000 : ℝ)^4529 ≤ (43911709222801/100000000000000 : ℝ)^3505 := by
    have hnat : (2644614571 : ℕ)^4529*100000000000000^3505 ≤ 43911709222801^3505*5000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644614571 5000000000 43911709222801 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (866821299/5000000000 : ℝ)^4529 ≤ (10390070965041/100000000000000 : ℝ)^3505 := by
    have hnat : (866821299 : ℕ)^4529*100000000000000^3505 ≤ 10390070965041^3505*5000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866821299 5000000000 10390070965041 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1091001963/2000000000 : ℝ)^4529 ≤ (2284910989863/5000000000000 : ℝ)^3505 := by
    have hnat : (1091001963 : ℕ)^4529*5000000000000^3505 ≤ 2284910989863^3505*2000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091001963 2000000000 2284910989863 5000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644614571/5000000000 : ℝ), (-866821299/5000000000 : ℝ), (1091001963/2000000000 : ℝ)] ![(43911709222801/100000000000000 : ℝ), (10390070965041/100000000000000 : ℝ), (2284910989863/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644614571/5000000000 : ℝ)|^4529 ≤ (43911709222801/100000000000000 : ℝ)^3505
        have hw : |(2644614571/5000000000 : ℝ)|=(2644614571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-866821299/5000000000 : ℝ)|^4529 ≤ (10390070965041/100000000000000 : ℝ)^3505
        have hw : |(-866821299/5000000000 : ℝ)|=(866821299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1091001963/2000000000 : ℝ)|^4529 ≤ (2284910989863/5000000000000 : ℝ)^3505
        have hw : |(1091001963/2000000000 : ℝ)|=(1091001963/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_s2_6 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (528923/1000000 : ℝ)*x 0 + (681876137/1250000000 : ℝ)*x 1 + (-866821207/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528923/1000000 : ℝ)^4529 ≤ (1756468737083/4000000000000 : ℝ)^3505 := by
    have hnat : (528923 : ℕ)^4529*4000000000000^3505 ≤ 1756468737083^3505*1000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528923 1000000 1756468737083 4000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (681876137/1250000000 : ℝ)^4529 ≤ (22849106007131/50000000000000 : ℝ)^3505 := by
    have hnat : (681876137 : ℕ)^4529*50000000000000^3505 ≤ 22849106007131^3505*1250000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681876137 1250000000 22849106007131 50000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (866821207/5000000000 : ℝ)^4529 ≤ (10390069540119/100000000000000 : ℝ)^3505 := by
    have hnat : (866821207 : ℕ)^4529*100000000000000^3505 ≤ 10390069540119^3505*5000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866821207 5000000000 10390069540119 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528923/1000000 : ℝ), (681876137/1250000000 : ℝ), (-866821207/5000000000 : ℝ)] ![(1756468737083/4000000000000 : ℝ), (22849106007131/50000000000000 : ℝ), (10390069540119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528923/1000000 : ℝ)|^4529 ≤ (1756468737083/4000000000000 : ℝ)^3505
        have hw : |(528923/1000000 : ℝ)|=(528923/1000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(681876137/1250000000 : ℝ)|^4529 ≤ (22849106007131/50000000000000 : ℝ)^3505
        have hw : |(681876137/1250000000 : ℝ)|=(681876137/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-866821207/5000000000 : ℝ)|^4529 ≤ (10390069540119/100000000000000 : ℝ)^3505
        have hw : |(-866821207/5000000000 : ℝ)|=(866821207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_s2_7 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4265555593/10000000000 : ℝ)*x 0 + (456630241/1000000000 : ℝ)*x 1 + (796391663/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4265555593/10000000000 : ℝ)^4529 ≤ (33256112109459/100000000000000 : ℝ)^3505 := by
    have hnat : (4265555593 : ℕ)^4529*100000000000000^3505 ≤ 33256112109459^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4265555593 10000000000 33256112109459 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (456630241/1000000000 : ℝ)^4529 ≤ (9079148358711/25000000000000 : ℝ)^3505 := by
    have hnat : (456630241 : ℕ)^4529*25000000000000^3505 ≤ 9079148358711^3505*1000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456630241 1000000000 9079148358711 25000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (796391663/2000000000 : ℝ)^4529 ≤ (30427294438619/100000000000000 : ℝ)^3505 := by
    have hnat : (796391663 : ℕ)^4529*100000000000000^3505 ≤ 30427294438619^3505*2000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      796391663 2000000000 30427294438619 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4265555593/10000000000 : ℝ), (456630241/1000000000 : ℝ), (796391663/2000000000 : ℝ)] ![(33256112109459/100000000000000 : ℝ), (9079148358711/25000000000000 : ℝ), (30427294438619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4265555593/10000000000 : ℝ)|^4529 ≤ (33256112109459/100000000000000 : ℝ)^3505
        have hw : |(4265555593/10000000000 : ℝ)|=(4265555593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(456630241/1000000000 : ℝ)|^4529 ≤ (9079148358711/25000000000000 : ℝ)^3505
        have hw : |(456630241/1000000000 : ℝ)|=(456630241/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(796391663/2000000000 : ℝ)|^4529 ≤ (30427294438619/100000000000000 : ℝ)^3505
        have hw : |(796391663/2000000000 : ℝ)|=(796391663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1516_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20462363/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18289/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (841/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (1309/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15981/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18289/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (841/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18289/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (841/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18289/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (841/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18289/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (841/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18289/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (841/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18289/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (841/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (841/10000 : ℝ) ^ (4527/1024 : ℝ) ≤ (176454321013319/10000000000000000000 : ℝ) := by
    have hpowers : (841/10000 : ℝ)^4527 ≤ (176454321013319/10000000000000000000 : ℝ)^1024 := by
      have hnat : (841 : ℕ)^4527*10000000000000000000^1024 ≤ 176454321013319^1024*10000^4527 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        841 10000 176454321013319 10000000000000000000 4527 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (841/10000 : ℝ)) (X := (176454321013319/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4527 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18289/100000 : ℝ) ^ (4527/1024 : ℝ) ≤ (3420556464960033/6250000000000000000 : ℝ) := by
    have hpowers : (18289/100000 : ℝ)^4527 ≤ (3420556464960033/6250000000000000000 : ℝ)^1024 := by
      have hnat : (18289 : ℕ)^4527*6250000000000000000^1024 ≤ 3420556464960033^1024*100000^4527 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18289 100000 3420556464960033 6250000000000000000 4527 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18289/100000 : ℝ)) (X := (3420556464960033/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4527 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000176454321013319/5000000000000000000 : ℝ) ≤ (2500019956567001/2500000000000000 : ℝ) ^ (4527/1024 : ℝ) := by
    have hpowers : (5000176454321013319/5000000000000000000 : ℝ)^1024 ≤ (2500019956567001/2500000000000000 : ℝ)^4527 := by
      have hnat : (5000176454321013319 : ℕ)^1024*2500000000000000^4527 ≤ 2500019956567001^4527*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000176454321013319 5000000000000000000 2500019956567001 2500000000000000 1024 4527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500019956567001/2500000000000000 : ℝ)) (X := (5000176454321013319/5000000000000000000 : ℝ)) (by norm_num) 4527 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50028246723324746859/50000000000000000000 : ℝ) ≤ (10001277593312639/10000000000000000 : ℝ) ^ (4527/1024 : ℝ) := by
    have hpowers : (50028246723324746859/50000000000000000000 : ℝ)^1024 ≤ (10001277593312639/10000000000000000 : ℝ)^4527 := by
      have hnat : (50028246723324746859 : ℕ)^1024*10000000000000000^4527 ≤ 10001277593312639^4527*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028246723324746859 50000000000000000000 10001277593312639 10000000000000000 1024 4527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001277593312639/10000000000000000 : ℝ)) (X := (50028246723324746859/50000000000000000000 : ℝ)) (by norm_num) 4527 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3128420556464960033/3125000000000000000 : ℝ) ≤ (5001237680178637/5000000000000000 : ℝ) ^ (4527/1024 : ℝ) := by
    have hpowers : (3128420556464960033/3125000000000000000 : ℝ)^1024 ≤ (5001237680178637/5000000000000000 : ℝ)^4527 := by
      have hnat : (3128420556464960033 : ℕ)^1024*5000000000000000^4527 ≤ 5001237680178637^4527*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3128420556464960033 3125000000000000000 5001237680178637 5000000000000000 1024 4527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001237680178637/5000000000000000 : ℝ)) (X := (3128420556464960033/3125000000000000000 : ℝ)) (by norm_num) 4527 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(176454321013319/10000000000000000000 : ℝ) ≤ ((64303803490892481/64316406250000000 : ℝ)+2*(79851136309/65860000000000 : ℝ)*(841/10000 : ℝ))^(4527/1024 : ℝ) := by
    rw [show (64303803490892481/64316406250000000 : ℝ)+2*(79851136309/65860000000000 : ℝ)*(841/10000 : ℝ)=(2500019956567001/2500000000000000 : ℝ) by norm_num, show 1+2*(176454321013319/10000000000000000000 : ℝ)=(5000176454321013319/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3420556464960033/6250000000000000000 : ℝ)+(176454321013319/10000000000000000000 : ℝ) ≤ ((64303803490892481/64316406250000000 : ℝ)+(79851136309/65860000000000 : ℝ)*((18289/100000 : ℝ)+(841/10000 : ℝ)))^(4527/1024 : ℝ) := by
    rw [show (64303803490892481/64316406250000000 : ℝ)+(79851136309/65860000000000 : ℝ)*((18289/100000 : ℝ)+(841/10000 : ℝ))=(10001277593312639/10000000000000000 : ℝ) by norm_num, show 1+(3420556464960033/6250000000000000000 : ℝ)+(176454321013319/10000000000000000000 : ℝ)=(50028246723324746859/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3420556464960033/6250000000000000000 : ℝ) ≤ ((64303803490892481/64316406250000000 : ℝ)+2*(79851136309/65860000000000 : ℝ)*(18289/100000 : ℝ))^(4527/1024 : ℝ) := by
    rw [show (64303803490892481/64316406250000000 : ℝ)+2*(79851136309/65860000000000 : ℝ)*(18289/100000 : ℝ)=(5001237680178637/5000000000000000 : ℝ) by norm_num, show 1+2*(3420556464960033/6250000000000000000 : ℝ)=(3128420556464960033/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (64303803490892481/64316406250000000 : ℝ)*(X 1 0+X 2 0)+(79851136309/65860000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4527/1024 : ℝ)) (lo := (841/10000 : ℝ)) (hi := (18289/100000 : ℝ)) (c := (64303803490892481/64316406250000000 : ℝ)) (alpha := (79851136309/65860000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (64303803490892481/64316406250000000 : ℝ)*(X 0 1+X 2 1)+(79851136309/65860000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4527/1024 : ℝ)) (lo := (841/10000 : ℝ)) (hi := (18289/100000 : ℝ)) (c := (64303803490892481/64316406250000000 : ℝ)) (alpha := (79851136309/65860000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (64303803490892481/64316406250000000 : ℝ)*(X 0 2+X 1 2)+(79851136309/65860000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4527/1024 : ℝ)) (lo := (841/10000 : ℝ)) (hi := (18289/100000 : ℝ)) (c := (64303803490892481/64316406250000000 : ℝ)) (alpha := (79851136309/65860000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-929152551/5000000000 : ℝ)*X 0 0+(2728322153/5000000000 : ℝ)*X 0 1+(1299104639/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5357599573/10000000000 : ℝ)*X 1 0+(-498058107/2500000000 : ℝ)*X 1 1+(2598209599/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5357600409/10000000000 : ℝ)*X 2 0+(5196418667/10000000000 : ℝ)*X 2 1+(-398446403/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4265438721/10000000000 : ℝ)*X 0 0+(795647979/2000000000 : ℝ)*X 0 1+(4569988659/10000000000 : ℝ)*X 0 2+(4265438721/10000000000 : ℝ)*X 1 0+(795647979/2000000000 : ℝ)*X 1 1+(4569988659/10000000000 : ℝ)*X 1 2+(4265438721/10000000000 : ℝ)*X 2 0+(795647979/2000000000 : ℝ)*X 2 1+(4569988659/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-929177499/5000000000 : ℝ)*X 0 0+(649755057/1250000000 : ℝ)*X 0 1+(2727504413/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2644614571/5000000000 : ℝ)*X 1 0+(-866821299/5000000000 : ℝ)*X 1 1+(1091001963/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((528923/1000000 : ℝ)*X 2 0+(681876137/1250000000 : ℝ)*X 2 1+(-866821207/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4265555593/10000000000 : ℝ)*X 0 0+(456630241/1000000000 : ℝ)*X 0 1+(796391663/2000000000 : ℝ)*X 0 2+(4265555593/10000000000 : ℝ)*X 1 0+(456630241/1000000000 : ℝ)*X 1 1+(796391663/2000000000 : ℝ)*X 1 2+(4265555593/10000000000 : ℝ)*X 2 0+(456630241/1000000000 : ℝ)*X 2 1+(796391663/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (461483610932121649893287103/51453125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1811277919/100000000000000 : ℝ)*(base19) + (210892029/10000000000000 : ℝ)*(base23) + (35389843/25000000000000 : ℝ)*(upper3) + (80899909/50000000000000 : ℝ)*(upper4) + (36982459/10000000000000 : ℝ)*(upper5) + (2766409560254427/100000000000000 : ℝ)*(major0) + (2766409560254427/100000000000000 : ℝ)*(major1) + (2766409560254427/100000000000000 : ℝ)*(major2) + (960710841949433/25000000000000 : ℝ)*(sp0) + (3842879269291361/100000000000000 : ℝ)*(sp1) + (384287897164899/10000000000000 : ℝ)*(sp2) + (422480509769283/25000000000000 : ℝ)*(sp3) + (37712771547/100000000000000 : ℝ)*(sp4) + (15701895421/100000000000000 : ℝ)*(sp7) + (211242217621569/12500000000000 : ℝ)*(f.failure) + (12009003376779/312500000000 : ℝ)*(f.sum) + (2018571417693/823250000000000000000000000 : ℝ)*base66 + (577430624826363933/102906250000000000000000000000000 : ℝ)*base68 + (640136058738832683/102906250000000000000000000000000 : ℝ)*base70 + (1152572781784863933/102906250000000000000000000000000 : ℝ)*base72 + (1759949330037/3293000000000000000000000000 : ℝ)*base73 + (735814139162332683/102906250000000000000000000000000 : ℝ)*base76 + (1206315370900520183/102906250000000000000000000000000 : ℝ)*base78 + (1414930763934426433/102906250000000000000000000000000 : ℝ)*base80 + (1979692073843/1646500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (679953/156250000000000000000 : ℝ)*base90 + (679953/156250000000000000000 : ℝ)*base92 + (679953/156250000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (289043338512498723058330131/51453125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (230611549/50000000000000 : ℝ)*(base15) + (128322699/50000000000000 : ℝ)*(lower2) + (19393519/100000000000000 : ℝ)*(upper3) + (70740753/50000000000000 : ℝ)*(lower4) + (1400715284189603/50000000000000 : ℝ)*(major0) + (1400715284189603/50000000000000 : ℝ)*(major1) + (1400715284189603/50000000000000 : ℝ)*(major2) + (2201957539/50000000000000 : ℝ)*(sp1) + (838141461/20000000000000 : ℝ)*(sp2) + (2622836733/50000000000000 : ℝ)*(sp3) + (1945764828884961/50000000000000 : ℝ)*(sp4) + (1945762396315873/50000000000000 : ℝ)*(sp5) + (1945762733531309/50000000000000 : ℝ)*(sp6) + (855663023030757/50000000000000 : ℝ)*(sp7) + (1711331291734981/100000000000000 : ℝ)*(f.failure) + (1945764828884961/50000000000000 : ℝ)*(f.sum) + (5001305743739/1646500000000000000000000000 : ℝ)*base65 + (82497521585653813/51453125000000000000000000000000 : ℝ)*base67 + (152072301521564937/51453125000000000000000000000000 : ℝ)*base70 + (41843543154908687/51453125000000000000000000000000 : ℝ)*base72 + (172474290081/41162500000000000000000000 : ℝ)*base73 + (39087560655408687/51453125000000000000000000000000 : ℝ)*base76 + (98945910826415281/25726562500000000000000000000000 : ℝ)*base78 + (162785296183602781/25726562500000000000000000000000 : ℝ)*base80 + (3889792717593/3293000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (6020103/1250000000000000000000 : ℝ)*base89 + (6020103/1250000000000000000000 : ℝ)*base91 + (6020103/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1516_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20462363/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18289/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (841/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1309/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15981/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1516_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1516_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20462363/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1309/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15981/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1516_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1516_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1516_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20462363/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1309/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15981/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1516_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

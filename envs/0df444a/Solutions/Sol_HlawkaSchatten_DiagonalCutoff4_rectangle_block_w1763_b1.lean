-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1763_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:29:13.938905+00:00
-- url     : https://prove2.me/submissions/c3d4d490-4189-42bf-a331-8f2fd8d8a173

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
theorem support_rectangle_w1763_box_0 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-787069359/10000000000 : ℝ)*x 0 + (5411625451/10000000000 : ℝ)*x 1 + (42278323/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (787069359/10000000000 : ℝ)^5983 ≤ (4656366423353/100000000000000 : ℝ)^4959 := by
    have hnat : (787069359 : ℕ)^5983*100000000000000^4959 ≤ 4656366423353^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      787069359 10000000000 4656366423353 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411625451/10000000000 : ℝ)^5983 ≤ (47671817349433/100000000000000 : ℝ)^4959 := by
    have hnat : (5411625451 : ℕ)^5983*100000000000000^4959 ≤ 47671817349433^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411625451 10000000000 47671817349433 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42278323/78125000 : ℝ)^5983 ≤ (23835908106109/50000000000000 : ℝ)^4959 := by
    have hnat : (42278323 : ℕ)^5983*50000000000000^4959 ≤ 23835908106109^4959*78125000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42278323 78125000 23835908106109 50000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-787069359/10000000000 : ℝ), (5411625451/10000000000 : ℝ), (42278323/78125000 : ℝ)] ![(4656366423353/100000000000000 : ℝ), (47671817349433/100000000000000 : ℝ), (23835908106109/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-787069359/10000000000 : ℝ)|^5983 ≤ (4656366423353/100000000000000 : ℝ)^4959
        have hw : |(-787069359/10000000000 : ℝ)|=(787069359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411625451/10000000000 : ℝ)|^5983 ≤ (47671817349433/100000000000000 : ℝ)^4959
        have hw : |(5411625451/10000000000 : ℝ)|=(5411625451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42278323/78125000 : ℝ)|^5983 ≤ (23835908106109/50000000000000 : ℝ)^4959
        have hw : |(42278323/78125000 : ℝ)|=(42278323/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1763_box_1 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1014232/1953125 : ℝ)*x 0 + (-54987683/500000000 : ℝ)*x 1 + (5411625481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1014232/1953125 : ℝ)^5983 ≤ (226783157617/500000000000 : ℝ)^4959 := by
    have hnat : (1014232 : ℕ)^5983*500000000000^4959 ≤ 226783157617^4959*1953125^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1014232 1953125 226783157617 500000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54987683/500000000 : ℝ)^5983 ≤ (3485775396039/50000000000000 : ℝ)^4959 := by
    have hnat : (54987683 : ℕ)^5983*50000000000000^4959 ≤ 3485775396039^4959*500000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54987683 500000000 3485775396039 50000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411625481/10000000000 : ℝ)^5983 ≤ (23835908834139/50000000000000 : ℝ)^4959 := by
    have hnat : (5411625481 : ℕ)^5983*50000000000000^4959 ≤ 23835908834139^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411625481 10000000000 23835908834139 50000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1014232/1953125 : ℝ), (-54987683/500000000 : ℝ), (5411625481/10000000000 : ℝ)] ![(226783157617/500000000000 : ℝ), (3485775396039/50000000000000 : ℝ), (23835908834139/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1014232/1953125 : ℝ)|^5983 ≤ (226783157617/500000000000 : ℝ)^4959
        have hw : |(1014232/1953125 : ℝ)|=(1014232/1953125 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-54987683/500000000 : ℝ)|^5983 ≤ (3485775396039/50000000000000 : ℝ)^4959
        have hw : |(-54987683/500000000 : ℝ)|=(54987683/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411625481/10000000000 : ℝ)|^5983 ≤ (23835908834139/50000000000000 : ℝ)^4959
        have hw : |(5411625481/10000000000 : ℝ)|=(5411625481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1763_box_2 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5192867637/10000000000 : ℝ)*x 0 + (2705812803/5000000000 : ℝ)*x 1 + (-549876883/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5192867637/10000000000 : ℝ)^5983 ≤ (9071325876837/20000000000000 : ℝ)^4959 := by
    have hnat : (5192867637 : ℕ)^5983*20000000000000^4959 ≤ 9071325876837^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5192867637 10000000000 9071325876837 20000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705812803/5000000000 : ℝ)^5983 ≤ (47671818996801/100000000000000 : ℝ)^4959 := by
    have hnat : (2705812803 : ℕ)^5983*100000000000000^4959 ≤ 47671818996801^4959*5000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705812803 5000000000 47671818996801 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (549876883/5000000000 : ℝ)^5983 ≤ (3485775801393/50000000000000 : ℝ)^4959 := by
    have hnat : (549876883 : ℕ)^5983*50000000000000^4959 ≤ 3485775801393^4959*5000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549876883 5000000000 3485775801393 50000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5192867637/10000000000 : ℝ), (2705812803/5000000000 : ℝ), (-549876883/5000000000 : ℝ)] ![(9071325876837/20000000000000 : ℝ), (47671818996801/100000000000000 : ℝ), (3485775801393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5192867637/10000000000 : ℝ)|^5983 ≤ (9071325876837/20000000000000 : ℝ)^4959
        have hw : |(5192867637/10000000000 : ℝ)|=(5192867637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705812803/5000000000 : ℝ)|^5983 ≤ (47671818996801/100000000000000 : ℝ)^4959
        have hw : |(2705812803/5000000000 : ℝ)|=(2705812803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-549876883/5000000000 : ℝ)|^5983 ≤ (3485775801393/50000000000000 : ℝ)^4959
        have hw : |(-549876883/5000000000 : ℝ)|=(549876883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1763_box_3 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4519195777/10000000000 : ℝ)*x 0 + (1885007111/5000000000 : ℝ)*x 1 + (942503371/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4519195777/10000000000 : ℝ)^5983 ≤ (19178013461143/50000000000000 : ℝ)^4959 := by
    have hnat : (4519195777 : ℕ)^5983*50000000000000^4959 ≤ 19178013461143^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4519195777 10000000000 19178013461143 50000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1885007111/5000000000 : ℝ)^5983 ≤ (7705497543313/25000000000000 : ℝ)^4959 := by
    have hnat : (1885007111 : ℕ)^5983*25000000000000^4959 ≤ 7705497543313^4959*5000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1885007111 5000000000 7705497543313 25000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (942503371/2500000000 : ℝ)^5983 ≤ (7705495723449/25000000000000 : ℝ)^4959 := by
    have hnat : (942503371 : ℕ)^5983*25000000000000^4959 ≤ 7705495723449^4959*2500000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      942503371 2500000000 7705495723449 25000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4519195777/10000000000 : ℝ), (1885007111/5000000000 : ℝ), (942503371/2500000000 : ℝ)] ![(19178013461143/50000000000000 : ℝ), (7705497543313/25000000000000 : ℝ), (7705495723449/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4519195777/10000000000 : ℝ)|^5983 ≤ (19178013461143/50000000000000 : ℝ)^4959
        have hw : |(4519195777/10000000000 : ℝ)|=(4519195777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1885007111/5000000000 : ℝ)|^5983 ≤ (7705497543313/25000000000000 : ℝ)^4959
        have hw : |(1885007111/5000000000 : ℝ)|=(1885007111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(942503371/2500000000 : ℝ)|^5983 ≤ (7705495723449/25000000000000 : ℝ)^4959
        have hw : |(942503371/2500000000 : ℝ)|=(942503371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1763_box_4 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-311707671/2000000000 : ℝ)*x 0 + (51296511/100000000 : ℝ)*x 1 + (205186009/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (311707671/2000000000 : ℝ)^5983 ≤ (2123484554153/20000000000000 : ℝ)^4959 := by
    have hnat : (311707671 : ℕ)^5983*20000000000000^4959 ≤ 2123484554153^4959*2000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      311707671 2000000000 2123484554153 20000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (51296511/100000000 : ℝ)^5983 ≤ (44691293204029/100000000000000 : ℝ)^4959 := by
    have hnat : (51296511 : ℕ)^5983*100000000000000^4959 ≤ 44691293204029^4959*100000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51296511 100000000 44691293204029 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (205186009/400000000 : ℝ)^5983 ≤ (22345642003283/50000000000000 : ℝ)^4959 := by
    have hnat : (205186009 : ℕ)^5983*50000000000000^4959 ≤ 22345642003283^4959*400000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205186009 400000000 22345642003283 50000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-311707671/2000000000 : ℝ), (51296511/100000000 : ℝ), (205186009/400000000 : ℝ)] ![(2123484554153/20000000000000 : ℝ), (44691293204029/100000000000000 : ℝ), (22345642003283/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-311707671/2000000000 : ℝ)|^5983 ≤ (2123484554153/20000000000000 : ℝ)^4959
        have hw : |(-311707671/2000000000 : ℝ)|=(311707671/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(51296511/100000000 : ℝ)|^5983 ≤ (44691293204029/100000000000000 : ℝ)^4959
        have hw : |(51296511/100000000 : ℝ)|=(51296511/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(205186009/400000000 : ℝ)|^5983 ≤ (22345642003283/50000000000000 : ℝ)^4959
        have hw : |(205186009/400000000 : ℝ)|=(205186009/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1763_box_5 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5380614943/10000000000 : ℝ)*x 0 + (-19192327/156250000 : ℝ)*x 1 + (2564825333/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380614943/10000000000 : ℝ)^5983 ≤ (47342427402157/100000000000000 : ℝ)^4959 := by
    have hnat : (5380614943 : ℕ)^5983*100000000000000^4959 ≤ 47342427402157^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380614943 10000000000 47342427402157 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (19192327/156250000 : ℝ)^5983 ≤ (7966283940137/100000000000000 : ℝ)^4959 := by
    have hnat : (19192327 : ℕ)^5983*100000000000000^4959 ≤ 7966283940137^4959*156250000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19192327 156250000 7966283940137 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2564825333/5000000000 : ℝ)^5983 ≤ (5586411080261/12500000000000 : ℝ)^4959 := by
    have hnat : (2564825333 : ℕ)^5983*12500000000000^4959 ≤ 5586411080261^4959*5000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2564825333 5000000000 5586411080261 12500000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380614943/10000000000 : ℝ), (-19192327/156250000 : ℝ), (2564825333/5000000000 : ℝ)] ![(47342427402157/100000000000000 : ℝ), (7966283940137/100000000000000 : ℝ), (5586411080261/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380614943/10000000000 : ℝ)|^5983 ≤ (47342427402157/100000000000000 : ℝ)^4959
        have hw : |(5380614943/10000000000 : ℝ)|=(5380614943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-19192327/156250000 : ℝ)|^5983 ≤ (7966283940137/100000000000000 : ℝ)^4959
        have hw : |(-19192327/156250000 : ℝ)|=(19192327/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2564825333/5000000000 : ℝ)|^5983 ≤ (5586411080261/12500000000000 : ℝ)^4959
        have hw : |(2564825333/5000000000 : ℝ)|=(2564825333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1763_box_6 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (672576787/1250000000 : ℝ)*x 0 + (5129651381/10000000000 : ℝ)*x 1 + (-614154423/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672576787/1250000000 : ℝ)^5983 ≤ (47342420533881/100000000000000 : ℝ)^4959 := by
    have hnat : (672576787 : ℕ)^5983*100000000000000^4959 ≤ 47342420533881^4959*1250000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672576787 1250000000 47342420533881 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5129651381/10000000000 : ℝ)^5983 ≤ (44691296157729/100000000000000 : ℝ)^4959 := by
    have hnat : (5129651381 : ℕ)^5983*100000000000000^4959 ≤ 44691296157729^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129651381 10000000000 44691296157729 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (614154423/5000000000 : ℝ)^5983 ≤ (7966283298503/100000000000000 : ℝ)^4959 := by
    have hnat : (614154423 : ℕ)^5983*100000000000000^4959 ≤ 7966283298503^4959*5000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      614154423 5000000000 7966283298503 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672576787/1250000000 : ℝ), (5129651381/10000000000 : ℝ), (-614154423/5000000000 : ℝ)] ![(47342420533881/100000000000000 : ℝ), (44691296157729/100000000000000 : ℝ), (7966283298503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672576787/1250000000 : ℝ)|^5983 ≤ (47342420533881/100000000000000 : ℝ)^4959
        have hw : |(672576787/1250000000 : ℝ)|=(672576787/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5129651381/10000000000 : ℝ)|^5983 ≤ (44691296157729/100000000000000 : ℝ)^4959
        have hw : |(5129651381/10000000000 : ℝ)|=(5129651381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-614154423/5000000000 : ℝ)|^5983 ≤ (7966283298503/100000000000000 : ℝ)^4959
        have hw : |(-614154423/5000000000 : ℝ)|=(614154423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1763_box_7 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3431564811/10000000000 : ℝ)*x 0 + (172471421/400000000 : ℝ)*x 1 + (2155892287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3431564811/10000000000 : ℝ)^5983 ≤ (27515314687023/100000000000000 : ℝ)^4959 := by
    have hnat : (3431564811 : ℕ)^5983*100000000000000^4959 ≤ 27515314687023^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3431564811 10000000000 27515314687023 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (172471421/400000000 : ℝ)^5983 ≤ (3624234746789/10000000000000 : ℝ)^4959 := by
    have hnat : (172471421 : ℕ)^5983*10000000000000^4959 ≤ 3624234746789^4959*400000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172471421 400000000 3624234746789 10000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2155892287/5000000000 : ℝ)^5983 ≤ (36242337823727/100000000000000 : ℝ)^4959 := by
    have hnat : (2155892287 : ℕ)^5983*100000000000000^4959 ≤ 36242337823727^4959*5000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155892287 5000000000 36242337823727 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3431564811/10000000000 : ℝ), (172471421/400000000 : ℝ), (2155892287/5000000000 : ℝ)] ![(27515314687023/100000000000000 : ℝ), (3624234746789/10000000000000 : ℝ), (36242337823727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3431564811/10000000000 : ℝ)|^5983 ≤ (27515314687023/100000000000000 : ℝ)^4959
        have hw : |(3431564811/10000000000 : ℝ)|=(3431564811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(172471421/400000000 : ℝ)|^5983 ≤ (3624234746789/10000000000000 : ℝ)^4959
        have hw : |(172471421/400000000 : ℝ)|=(172471421/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2155892287/5000000000 : ℝ)|^5983 ≤ (36242337823727/100000000000000 : ℝ)^4959
        have hw : |(2155892287/5000000000 : ℝ)|=(2155892287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1763_box_8 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-695234957/5000000000 : ℝ)*x 0 + (4913688493/10000000000 : ℝ)*x 1 + (5472251791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (695234957/5000000000 : ℝ)^5983 ≤ (9251885604539/100000000000000 : ℝ)^4959 := by
    have hnat : (695234957 : ℕ)^5983*100000000000000^4959 ≤ 9251885604539^4959*5000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      695234957 5000000000 9251885604539 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4913688493/10000000000 : ℝ)^5983 ≤ (1697248252651/4000000000000 : ℝ)^4959 := by
    have hnat : (4913688493 : ℕ)^5983*4000000000000^4959 ≤ 1697248252651^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4913688493 10000000000 1697248252651 4000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5472251791/10000000000 : ℝ)^5983 ≤ (24158454030637/50000000000000 : ℝ)^4959 := by
    have hnat : (5472251791 : ℕ)^5983*50000000000000^4959 ≤ 24158454030637^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5472251791 10000000000 24158454030637 50000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-695234957/5000000000 : ℝ), (4913688493/10000000000 : ℝ), (5472251791/10000000000 : ℝ)] ![(9251885604539/100000000000000 : ℝ), (1697248252651/4000000000000 : ℝ), (24158454030637/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-695234957/5000000000 : ℝ)|^5983 ≤ (9251885604539/100000000000000 : ℝ)^4959
        have hw : |(-695234957/5000000000 : ℝ)|=(695234957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4913688493/10000000000 : ℝ)|^5983 ≤ (1697248252651/4000000000000 : ℝ)^4959
        have hw : |(4913688493/10000000000 : ℝ)|=(4913688493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5472251791/10000000000 : ℝ)|^5983 ≤ (24158454030637/50000000000000 : ℝ)^4959
        have hw : |(5472251791/10000000000 : ℝ)|=(5472251791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1763_box_9 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (515257667/1000000000 : ℝ)*x 0 + (-535399041/5000000000 : ℝ)*x 1 + (684031579/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (515257667/1000000000 : ℝ)^5983 ≤ (22466191893391/50000000000000 : ℝ)^4959 := by
    have hnat : (515257667 : ℕ)^5983*50000000000000^4959 ≤ 22466191893391^4959*1000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515257667 1000000000 22466191893391 50000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (535399041/5000000000 : ℝ)^5983 ≤ (1350139835547/20000000000000 : ℝ)^4959 := by
    have hnat : (535399041 : ℕ)^5983*20000000000000^4959 ≤ 1350139835547^4959*5000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535399041 5000000000 1350139835547 20000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (684031579/1250000000 : ℝ)^5983 ≤ (48316917020159/100000000000000 : ℝ)^4959 := by
    have hnat : (684031579 : ℕ)^5983*100000000000000^4959 ≤ 48316917020159^4959*1250000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684031579 1250000000 48316917020159 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(515257667/1000000000 : ℝ), (-535399041/5000000000 : ℝ), (684031579/1250000000 : ℝ)] ![(22466191893391/50000000000000 : ℝ), (1350139835547/20000000000000 : ℝ), (48316917020159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(515257667/1000000000 : ℝ)|^5983 ≤ (22466191893391/50000000000000 : ℝ)^4959
        have hw : |(515257667/1000000000 : ℝ)|=(515257667/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-535399041/5000000000 : ℝ)|^5983 ≤ (1350139835547/20000000000000 : ℝ)^4959
        have hw : |(-535399041/5000000000 : ℝ)|=(535399041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(684031579/1250000000 : ℝ)|^5983 ≤ (48316917020159/100000000000000 : ℝ)^4959
        have hw : |(684031579/1250000000 : ℝ)|=(684031579/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1763_box_10 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (206103109/400000000 : ℝ)*x 0 + (342015787/625000000 : ℝ)*x 1 + (-1070796679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (206103109/400000000 : ℝ)^5983 ≤ (44932394886511/100000000000000 : ℝ)^4959 := by
    have hnat : (206103109 : ℕ)^5983*100000000000000^4959 ≤ 44932394886511^4959*400000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206103109 400000000 44932394886511 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (342015787/625000000 : ℝ)^5983 ≤ (48316916594053/100000000000000 : ℝ)^4959 := by
    have hnat : (342015787 : ℕ)^5983*100000000000000^4959 ≤ 48316916594053^4959*625000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342015787 625000000 48316916594053 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1070796679/10000000000 : ℝ)^5983 ≤ (6750688506279/100000000000000 : ℝ)^4959 := by
    have hnat : (1070796679 : ℕ)^5983*100000000000000^4959 ≤ 6750688506279^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070796679 10000000000 6750688506279 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(206103109/400000000 : ℝ), (342015787/625000000 : ℝ), (-1070796679/10000000000 : ℝ)] ![(44932394886511/100000000000000 : ℝ), (48316916594053/100000000000000 : ℝ), (6750688506279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(206103109/400000000 : ℝ)|^5983 ≤ (44932394886511/100000000000000 : ℝ)^4959
        have hw : |(206103109/400000000 : ℝ)|=(206103109/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(342015787/625000000 : ℝ)|^5983 ≤ (48316916594053/100000000000000 : ℝ)^4959
        have hw : |(342015787/625000000 : ℝ)|=(342015787/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1070796679/10000000000 : ℝ)|^5983 ≤ (6750688506279/100000000000000 : ℝ)^4959
        have hw : |(-1070796679/10000000000 : ℝ)|=(1070796679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1763_box_11 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (592823841/1250000000 : ℝ)*x 0 + (1826548047/5000000000 : ℝ)*x 1 + (456636691/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (592823841/1250000000 : ℝ)^5983 ≤ (40655103200481/100000000000000 : ℝ)^4959 := by
    have hnat : (592823841 : ℕ)^5983*100000000000000^4959 ≤ 40655103200481^4959*1250000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      592823841 1250000000 40655103200481 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1826548047/5000000000 : ℝ)^5983 ≤ (5934492193169/20000000000000 : ℝ)^4959 := by
    have hnat : (1826548047 : ℕ)^5983*20000000000000^4959 ≤ 5934492193169^4959*5000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1826548047 5000000000 5934492193169 20000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (456636691/1250000000 : ℝ)^5983 ≤ (29672435819551/100000000000000 : ℝ)^4959 := by
    have hnat : (456636691 : ℕ)^5983*100000000000000^4959 ≤ 29672435819551^4959*1250000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456636691 1250000000 29672435819551 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(592823841/1250000000 : ℝ), (1826548047/5000000000 : ℝ), (456636691/1250000000 : ℝ)] ![(40655103200481/100000000000000 : ℝ), (5934492193169/20000000000000 : ℝ), (29672435819551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(592823841/1250000000 : ℝ)|^5983 ≤ (40655103200481/100000000000000 : ℝ)^4959
        have hw : |(592823841/1250000000 : ℝ)|=(592823841/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1826548047/5000000000 : ℝ)|^5983 ≤ (5934492193169/20000000000000 : ℝ)^4959
        have hw : |(1826548047/5000000000 : ℝ)|=(1826548047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(456636691/1250000000 : ℝ)|^5983 ≤ (29672435819551/100000000000000 : ℝ)^4959
        have hw : |(456636691/1250000000 : ℝ)|=(456636691/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1763_box_12 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-235187421/2500000000 : ℝ)*x 0 + (1403852987/2500000000 : ℝ)*x 1 + (5099981461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (235187421/2500000000 : ℝ)^5983 ≤ (577435411197/10000000000000 : ℝ)^4959 := by
    have hnat : (235187421 : ℕ)^5983*10000000000000^4959 ≤ 577435411197^4959*2500000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235187421 2500000000 577435411197 10000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1403852987/2500000000 : ℝ)^5983 ≤ (49846035176119/100000000000000 : ℝ)^4959 := by
    have hnat : (1403852987 : ℕ)^5983*100000000000000^4959 ≤ 49846035176119^4959*2500000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1403852987 2500000000 49846035176119 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5099981461/10000000000 : ℝ)^5983 ≤ (346715708579/781250000000 : ℝ)^4959 := by
    have hnat : (5099981461 : ℕ)^5983*781250000000^4959 ≤ 346715708579^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5099981461 10000000000 346715708579 781250000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-235187421/2500000000 : ℝ), (1403852987/2500000000 : ℝ), (5099981461/10000000000 : ℝ)] ![(577435411197/10000000000000 : ℝ), (49846035176119/100000000000000 : ℝ), (346715708579/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-235187421/2500000000 : ℝ)|^5983 ≤ (577435411197/10000000000000 : ℝ)^4959
        have hw : |(-235187421/2500000000 : ℝ)|=(235187421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1403852987/2500000000 : ℝ)|^5983 ≤ (49846035176119/100000000000000 : ℝ)^4959
        have hw : |(1403852987/2500000000 : ℝ)|=(1403852987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5099981461/10000000000 : ℝ)|^5983 ≤ (346715708579/781250000000 : ℝ)^4959
        have hw : |(5099981461/10000000000 : ℝ)|=(5099981461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1763_box_13 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5400445327/10000000000 : ℝ)*x 0 + (-124121423/1000000000 : ℝ)*x 1 + (2549990559/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5400445327/10000000000 : ℝ)^5983 ≤ (23776509173153/50000000000000 : ℝ)^4959 := by
    have hnat : (5400445327 : ℕ)^5983*50000000000000^4959 ≤ 23776509173153^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400445327 10000000000 23776509173153 50000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (124121423/1000000000 : ℝ)^5983 ≤ (4033687272033/50000000000000 : ℝ)^4959 := by
    have hnat : (124121423 : ℕ)^5983*50000000000000^4959 ≤ 4033687272033^4959*1000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124121423 1000000000 4033687272033 50000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2549990559/5000000000 : ℝ)^5983 ≤ (44379607097023/100000000000000 : ℝ)^4959 := by
    have hnat : (2549990559 : ℕ)^5983*100000000000000^4959 ≤ 44379607097023^4959*5000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2549990559 5000000000 44379607097023 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5400445327/10000000000 : ℝ), (-124121423/1000000000 : ℝ), (2549990559/5000000000 : ℝ)] ![(23776509173153/50000000000000 : ℝ), (4033687272033/50000000000000 : ℝ), (44379607097023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5400445327/10000000000 : ℝ)|^5983 ≤ (23776509173153/50000000000000 : ℝ)^4959
        have hw : |(5400445327/10000000000 : ℝ)|=(5400445327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-124121423/1000000000 : ℝ)|^5983 ≤ (4033687272033/50000000000000 : ℝ)^4959
        have hw : |(-124121423/1000000000 : ℝ)|=(124121423/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2549990559/5000000000 : ℝ)|^5983 ≤ (44379607097023/100000000000000 : ℝ)^4959
        have hw : |(2549990559/5000000000 : ℝ)|=(2549990559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1763_box_14 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5400444957/10000000000 : ℝ)*x 0 + (5099980373/10000000000 : ℝ)*x 1 + (-1241215729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5400444957/10000000000 : ℝ)^5983 ≤ (47553014415559/100000000000000 : ℝ)^4959 := by
    have hnat : (5400444957 : ℕ)^5983*100000000000000^4959 ≤ 47553014415559^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400444957 10000000000 47553014415559 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5099980373/10000000000 : ℝ)^5983 ≤ (8875919855083/20000000000000 : ℝ)^4959 := by
    have hnat : (5099980373 : ℕ)^5983*20000000000000^4959 ≤ 8875919855083^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5099980373 10000000000 8875919855083 20000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1241215729/10000000000 : ℝ)^5983 ≤ (403369314939/5000000000000 : ℝ)^4959 := by
    have hnat : (1241215729 : ℕ)^5983*5000000000000^4959 ≤ 403369314939^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1241215729 10000000000 403369314939 5000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5400444957/10000000000 : ℝ), (5099980373/10000000000 : ℝ), (-1241215729/10000000000 : ℝ)] ![(47553014415559/100000000000000 : ℝ), (8875919855083/20000000000000 : ℝ), (403369314939/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5400444957/10000000000 : ℝ)|^5983 ≤ (47553014415559/100000000000000 : ℝ)^4959
        have hw : |(5400444957/10000000000 : ℝ)|=(5400444957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5099980373/10000000000 : ℝ)|^5983 ≤ (8875919855083/20000000000000 : ℝ)^4959
        have hw : |(5099980373/10000000000 : ℝ)|=(5099980373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1241215729/10000000000 : ℝ)|^5983 ≤ (403369314939/5000000000000 : ℝ)^4959
        have hw : |(-1241215729/10000000000 : ℝ)|=(1241215729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1763_box_15 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (827984597/2500000000 : ℝ)*x 0 + (4368557107/10000000000 : ℝ)*x 1 + (87371231/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (827984597/2500000000 : ℝ)^5983 ≤ (26362250074001/100000000000000 : ℝ)^4959 := by
    have hnat : (827984597 : ℕ)^5983*100000000000000^4959 ≤ 26362250074001^4959*2500000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827984597 2500000000 26362250074001 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4368557107/10000000000 : ℝ)^5983 ≤ (4602356545771/12500000000000 : ℝ)^4959 := by
    have hnat : (4368557107 : ℕ)^5983*12500000000000^4959 ≤ 4602356545771^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368557107 10000000000 4602356545771 12500000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (87371231/200000000 : ℝ)^5983 ≤ (18409448772421/50000000000000 : ℝ)^4959 := by
    have hnat : (87371231 : ℕ)^5983*50000000000000^4959 ≤ 18409448772421^4959*200000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87371231 200000000 18409448772421 50000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(827984597/2500000000 : ℝ), (4368557107/10000000000 : ℝ), (87371231/200000000 : ℝ)] ![(26362250074001/100000000000000 : ℝ), (4602356545771/12500000000000 : ℝ), (18409448772421/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(827984597/2500000000 : ℝ)|^5983 ≤ (26362250074001/100000000000000 : ℝ)^4959
        have hw : |(827984597/2500000000 : ℝ)|=(827984597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4368557107/10000000000 : ℝ)|^5983 ≤ (4602356545771/12500000000000 : ℝ)^4959
        have hw : |(4368557107/10000000000 : ℝ)|=(4368557107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(87371231/200000000 : ℝ)|^5983 ≤ (18409448772421/50000000000000 : ℝ)^4959
        have hw : |(87371231/200000000 : ℝ)|=(87371231/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1763_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (111508997/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (709/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4593/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(69169/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58747/100000 : ℝ) ∧ (82289/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (46567/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (709/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4593/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (709/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4593/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (709/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4593/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (709/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4593/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (709/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4593/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (709/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4593/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4593/50000 : ℝ) ^ (5967/1024 : ℝ) ≤ (45389339772947/50000000000000000000 : ℝ) := by
    have hpowers : (4593/50000 : ℝ)^5967 ≤ (45389339772947/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4593 : ℕ)^5967*50000000000000000000^1024 ≤ 45389339772947^1024*50000^5967 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4593 50000 45389339772947 50000000000000000000 5967 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4593/50000 : ℝ)) (X := (45389339772947/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5967 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (709/4000 : ℝ) ^ (5967/1024 : ℝ) ≤ (4182158661830249/100000000000000000000 : ℝ) := by
    have hpowers : (709/4000 : ℝ)^5967 ≤ (4182158661830249/100000000000000000000 : ℝ)^1024 := by
      have hnat : (709 : ℕ)^5967*100000000000000000000^1024 ≤ 4182158661830249^1024*4000^5967 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        709 4000 4182158661830249 100000000000000000000 5967 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (709/4000 : ℝ)) (X := (4182158661830249/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5967 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000045389339772947/25000000000000000000 : ℝ) ≤ (500000155785651/500000000000000 : ℝ) ^ (5967/1024 : ℝ) := by
    have hpowers : (25000045389339772947/25000000000000000000 : ℝ)^1024 ≤ (500000155785651/500000000000000 : ℝ)^5967 := by
      have hnat : (25000045389339772947 : ℕ)^1024*500000000000000^5967 ≤ 500000155785651^5967*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000045389339772947 25000000000000000000 500000155785651 500000000000000 1024 5967 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500000155785651/500000000000000 : ℝ)) (X := (25000045389339772947/25000000000000000000 : ℝ)) (by norm_num) 5967 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100004272937341376143/100000000000000000000 : ℝ) ≤ (5000036663402053/5000000000000000 : ℝ) ^ (5967/1024 : ℝ) := by
    have hpowers : (100004272937341376143/100000000000000000000 : ℝ)^1024 ≤ (5000036663402053/5000000000000000 : ℝ)^5967 := by
      have hnat : (100004272937341376143 : ℕ)^1024*5000000000000000^5967 ≤ 5000036663402053^5967*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100004272937341376143 100000000000000000000 5000036663402053 5000000000000000 1024 5967 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000036663402053/5000000000000000 : ℝ)) (X := (100004272937341376143/100000000000000000000 : ℝ)) (by norm_num) 5967 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50004182158661830249/50000000000000000000 : ℝ) ≤ (1250017942236899/1250000000000000 : ℝ) ^ (5967/1024 : ℝ) := by
    have hpowers : (50004182158661830249/50000000000000000000 : ℝ)^1024 ≤ (1250017942236899/1250000000000000 : ℝ)^5967 := by
      have hnat : (50004182158661830249 : ℕ)^1024*1250000000000000^5967 ≤ 1250017942236899^5967*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004182158661830249 50000000000000000000 1250017942236899 1250000000000000 1024 5967 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250017942236899/1250000000000000 : ℝ)) (X := (50004182158661830249/50000000000000000000 : ℝ)) (by norm_num) 5967 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(45389339772947/50000000000000000000 : ℝ) ≤ ((21347184171727011447/21347500000000000000 : ℝ)+2*(35105545543/426950000000000 : ℝ)*(4593/50000 : ℝ))^(5967/1024 : ℝ) := by
    rw [show (21347184171727011447/21347500000000000000 : ℝ)+2*(35105545543/426950000000000 : ℝ)*(4593/50000 : ℝ)=(500000155785651/500000000000000 : ℝ) by norm_num, show 1+2*(45389339772947/50000000000000000000 : ℝ)=(25000045389339772947/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4182158661830249/100000000000000000000 : ℝ)+(45389339772947/50000000000000000000 : ℝ) ≤ ((21347184171727011447/21347500000000000000 : ℝ)+(35105545543/426950000000000 : ℝ)*((709/4000 : ℝ)+(4593/50000 : ℝ)))^(5967/1024 : ℝ) := by
    rw [show (21347184171727011447/21347500000000000000 : ℝ)+(35105545543/426950000000000 : ℝ)*((709/4000 : ℝ)+(4593/50000 : ℝ))=(5000036663402053/5000000000000000 : ℝ) by norm_num, show 1+(4182158661830249/100000000000000000000 : ℝ)+(45389339772947/50000000000000000000 : ℝ)=(100004272937341376143/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4182158661830249/100000000000000000000 : ℝ) ≤ ((21347184171727011447/21347500000000000000 : ℝ)+2*(35105545543/426950000000000 : ℝ)*(709/4000 : ℝ))^(5967/1024 : ℝ) := by
    rw [show (21347184171727011447/21347500000000000000 : ℝ)+2*(35105545543/426950000000000 : ℝ)*(709/4000 : ℝ)=(1250017942236899/1250000000000000 : ℝ) by norm_num, show 1+2*(4182158661830249/100000000000000000000 : ℝ)=(50004182158661830249/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21347184171727011447/21347500000000000000 : ℝ)*(X 1 0+X 2 0)+(35105545543/426950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5967/1024 : ℝ)) (lo := (4593/50000 : ℝ)) (hi := (709/4000 : ℝ)) (c := (21347184171727011447/21347500000000000000 : ℝ)) (alpha := (35105545543/426950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21347184171727011447/21347500000000000000 : ℝ)*(X 0 1+X 2 1)+(35105545543/426950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5967/1024 : ℝ)) (lo := (4593/50000 : ℝ)) (hi := (709/4000 : ℝ)) (c := (21347184171727011447/21347500000000000000 : ℝ)) (alpha := (35105545543/426950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21347184171727011447/21347500000000000000 : ℝ)*(X 0 2+X 1 2)+(35105545543/426950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5967/1024 : ℝ)) (lo := (4593/50000 : ℝ)) (hi := (709/4000 : ℝ)) (c := (21347184171727011447/21347500000000000000 : ℝ)) (alpha := (35105545543/426950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-787069359/10000000000 : ℝ)*X 0 0+(5411625451/10000000000 : ℝ)*X 0 1+(42278323/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1014232/1953125 : ℝ)*X 1 0+(-54987683/500000000 : ℝ)*X 1 1+(5411625481/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5192867637/10000000000 : ℝ)*X 2 0+(2705812803/5000000000 : ℝ)*X 2 1+(-549876883/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4519195777/10000000000 : ℝ)*X 0 0+(1885007111/5000000000 : ℝ)*X 0 1+(942503371/2500000000 : ℝ)*X 0 2+(4519195777/10000000000 : ℝ)*X 1 0+(1885007111/5000000000 : ℝ)*X 1 1+(942503371/2500000000 : ℝ)*X 1 2+(4519195777/10000000000 : ℝ)*X 2 0+(1885007111/5000000000 : ℝ)*X 2 1+(942503371/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-311707671/2000000000 : ℝ)*X 0 0+(51296511/100000000 : ℝ)*X 0 1+(205186009/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5380614943/10000000000 : ℝ)*X 1 0+(-19192327/156250000 : ℝ)*X 1 1+(2564825333/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((672576787/1250000000 : ℝ)*X 2 0+(5129651381/10000000000 : ℝ)*X 2 1+(-614154423/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3431564811/10000000000 : ℝ)*X 0 0+(172471421/400000000 : ℝ)*X 0 1+(2155892287/5000000000 : ℝ)*X 0 2+(3431564811/10000000000 : ℝ)*X 1 0+(172471421/400000000 : ℝ)*X 1 1+(2155892287/5000000000 : ℝ)*X 1 2+(3431564811/10000000000 : ℝ)*X 2 0+(172471421/400000000 : ℝ)*X 2 1+(2155892287/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-695234957/5000000000 : ℝ)*X 0 0+(4913688493/10000000000 : ℝ)*X 0 1+(5472251791/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((515257667/1000000000 : ℝ)*X 1 0+(-535399041/5000000000 : ℝ)*X 1 1+(684031579/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((206103109/400000000 : ℝ)*X 2 0+(342015787/625000000 : ℝ)*X 2 1+(-1070796679/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((592823841/1250000000 : ℝ)*X 0 0+(1826548047/5000000000 : ℝ)*X 0 1+(456636691/1250000000 : ℝ)*X 0 2+(592823841/1250000000 : ℝ)*X 1 0+(1826548047/5000000000 : ℝ)*X 1 1+(456636691/1250000000 : ℝ)*X 1 2+(592823841/1250000000 : ℝ)*X 2 0+(1826548047/5000000000 : ℝ)*X 2 1+(456636691/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-235187421/2500000000 : ℝ)*X 0 0+(1403852987/2500000000 : ℝ)*X 0 1+(5099981461/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5400445327/10000000000 : ℝ)*X 1 0+(-124121423/1000000000 : ℝ)*X 1 1+(2549990559/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5400444957/10000000000 : ℝ)*X 2 0+(5099980373/10000000000 : ℝ)*X 2 1+(-1241215729/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((827984597/2500000000 : ℝ)*X 0 0+(4368557107/10000000000 : ℝ)*X 0 1+(87371231/200000000 : ℝ)*X 0 2+(827984597/2500000000 : ℝ)*X 1 0+(4368557107/10000000000 : ℝ)*X 1 1+(87371231/200000000 : ℝ)*X 1 2+(827984597/2500000000 : ℝ)*X 2 0+(4368557107/10000000000 : ℝ)*X 2 1+(87371231/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-69169/100000 : ℝ) ≤ (-14765268318411679361895378267939/21347500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (93905159/100000000000000 : ℝ)*(upper3) + (510211/5000000000000 : ℝ)*(lower4) + (5954729/100000000000000 : ℝ)*(lower5) + (43762212705079/4000000000000 : ℝ)*(major0) + (43762212705079/4000000000000 : ℝ)*(major1) + (43762212705079/4000000000000 : ℝ)*(major2) + (2362447071/100000000000000 : ℝ)*(sp1) + (132957897/50000000000000 : ℝ)*(sp3) + (430149114256559/25000000000000 : ℝ)*(sp4) + (1720595512794087/100000000000000 : ℝ)*(sp5) + (860284625388827/50000000000000 : ℝ)*(sp6) + (30660494725229/6250000000000 : ℝ)*(sp7) + (709107461/50000000000000 : ℝ)*(sp8) + (1789028969/6250000000000 : ℝ)*(sp14) + (245284090759729/50000000000000 : ℝ)*(f.failure) + (860298937620579/50000000000000 : ℝ)*(f.sum) + (5300146528191/2134750000000000000000000000 : ℝ)*base65 + (224656335897429313/85390000000000000000000000000000 : ℝ)*base67 + (210929651772370687/85390000000000000000000000000000 : ℝ)*base70 + (451608430289919313/85390000000000000000000000000000 : ℝ)*base71 + (4977291886681/4269500000000000000000000000 : ℝ)*base73 + (167168755613139313/85390000000000000000000000000000 : ℝ)*base75 + (422170037284829313/85390000000000000000000000000000 : ℝ)*base77 + (296273354139629313/85390000000000000000000000000000 : ℝ)*base79 + (12325781039289/4269500000000000000000000000 : ℝ)*base82 + (26218187/2500000000000000000000 : ℝ)*base90 + (26218187/2500000000000000000000 : ℝ)*base92 + (26218187/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58747/100000 : ℝ) ≤ (313538717235462041696505288710913/533687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12803309/100000000000000 : ℝ)*(lower0) + (5635289/50000000000000 : ℝ)*(upper1) + (18943619/100000000000000 : ℝ)*(upper2) + (7409899/20000000000000 : ℝ)*(upper3) + (784701/6250000000000 : ℝ)*(lower5) + (1225347359923207/100000000000000 : ℝ)*(major0) + (1225347359923207/100000000000000 : ℝ)*(major1) + (1225347359923207/100000000000000 : ℝ)*(major2) + (1881672767959143/100000000000000 : ℝ)*(sp0) + (1881672767959143/100000000000000 : ℝ)*(sp1) + (1881671742410243/100000000000000 : ℝ)*(sp2) + (549436969453159/100000000000000 : ℝ)*(sp3) + (10255489/1000000000000 : ℝ)*(sp6) + (908526327/50000000000000 : ℝ)*(sp11) + (549438786505813/100000000000000 : ℝ)*(f.failure) + (1881672767959143/100000000000000 : ℝ)*(f.sum) + (248874336431/1334218750000000000000000000 : ℝ)*base65 + (6938455804378249471/2134750000000000000000000000000000 : ℝ)*base68 + (6302480091115000529/2134750000000000000000000000000000 : ℝ)*base69 + (262368669418750529/2134750000000000000000000000000000 : ℝ)*base71 + (14940974436493/10673750000000000000000000000 : ℝ)*base73 + (7988073159977750529/2134750000000000000000000000000000 : ℝ)*base75 + (5128704057601500529/2134750000000000000000000000000000 : ℝ)*base77 + (8524467777013000529/2134750000000000000000000000000000 : ℝ)*base79 + (18149745596363/10673750000000000000000000000 : ℝ)*base81 + (7700439/5000000000000000000000 : ℝ)*base90 + (7700439/5000000000000000000000 : ℝ)*base92 + (7700439/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (82289/100000 : ℝ) ≤ (1756719741221691311382934113/2134750000000000000000000000 : ℝ) := by norm_num
    linear_combination (85945747/100000000000000 : ℝ)*(upper0) + (1340569/2000000000000 : ℝ)*(upper1) + (324479383/100000000000000 : ℝ)*(upper4) + (58576304049389/5000000000000 : ℝ)*(major0) + (58576304049389/5000000000000 : ℝ)*(major1) + (58576304049389/5000000000000 : ℝ)*(major2) + (32547220563/50000000000000 : ℝ)*(sp1) + (98752800569/100000000000000 : ℝ)*(sp2) + (21956999431/100000000000000 : ℝ)*(sp3) + (2583978637/50000000000000 : ℝ)*(sp4) + (895155416242853/50000000000000 : ℝ)*(sp8) + (358050181200371/20000000000000 : ℝ)*(sp9) + (1790217247642411/100000000000000 : ℝ)*(sp10) + (525283674163129/100000000000000 : ℝ)*(sp11) + (1641580097383/312500000000 : ℝ)*(f.failure) + (1790316000442981/100000000000000 : ℝ)*(f.sum) + (18251716090761/8539000000000000000000000000 : ℝ)*base65 + (150087847375530883/106737500000000000000000000000000 : ℝ)*base67 + (45171871271855883/106737500000000000000000000000000 : ℝ)*base69 + (244475137014431617/106737500000000000000000000000000 : ℝ)*base72 + (6355286163083/4269500000000000000000000000 : ℝ)*base74 + (545265595377269117/106737500000000000000000000000000 : ℝ)*base76 + (125832501825793383/106737500000000000000000000000000 : ℝ)*base77 + (213819427350119117/106737500000000000000000000000000 : ℝ)*base80 + (9966891824389/8539000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (29851/15625000000000000000 : ℝ)*base89 + (29851/15625000000000000000 : ℝ)*base91 + (29851/15625000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-46567/50000 : ℝ) ≤ (-497033484235847356528627418521647/533687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (34266187/50000000000000 : ℝ)*(upper3) + (337841833/100000000000000 : ℝ)*(lower4) + (39195651/20000000000000 : ℝ)*(upper5) + (1230395766183633/100000000000000 : ℝ)*(major0) + (1230395766183633/100000000000000 : ℝ)*(major1) + (1230395766183633/100000000000000 : ℝ)*(major2) + (4773077521/100000000000000 : ℝ)*(sp4) + (5030075589/10000000000000 : ℝ)*(sp5) + (184464472071/100000000000000 : ℝ)*(sp6) + (39064475741/100000000000000 : ℝ)*(sp7) + (485032068438763/25000000000000 : ℝ)*(sp12) + (485020686519171/25000000000000 : ℝ)*(sp13) + (969974291180251/50000000000000 : ℝ)*(sp14) + (137915849670573/25000000000000 : ℝ)*(sp15) + (34481403947377/6250000000000 : ℝ)*(f.failure) + (1940133046832573/100000000000000 : ℝ)*(f.sum) + (130674848925371/21347500000000000000000000000 : ℝ)*base66 + (10283735979527753049/2134750000000000000000000000000000 : ℝ)*base68 + (7783950203678746951/2134750000000000000000000000000000 : ℝ)*base69 + (23704722481597753049/2134750000000000000000000000000000 : ℝ)*base72 + (59886735647717/42695000000000000000000000000 : ℝ)*base74 + (15328544562682503049/2134750000000000000000000000000000 : ℝ)*base76 + (2093571233144753049/2134750000000000000000000000000000 : ℝ)*base78 + (7812598267437503049/2134750000000000000000000000000000 : ℝ)*base80 + (15377876654497/10673750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (3074131/312500000000000000000 : ℝ)*base90 + (3074131/312500000000000000000 : ℝ)*base92 + (3074131/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1763_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (111508997/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (709/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4593/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(69169/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58747/100000 : ℝ) else (82289/100000 : ℝ) ≤ X j i ∧ X j i ≤ (46567/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1763_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1763_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (111508997/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (709/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4593/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(69169/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58747/100000 : ℝ) else (82289/100000 : ℝ) ≤ X j i ∧ X j i ≤ (46567/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1763_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (111508997/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (709/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4593/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(69169/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58747/100000 : ℝ) else (82289/100000 : ℝ) ≤ X j i ∧ X j i ≤ (46567/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1763_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

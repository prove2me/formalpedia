-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1222_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:11:33.002004+00:00
-- url     : https://prove2.me/submissions/c51c714f-7769-463a-815b-47f6da599715

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
theorem support_rectangle_w1222_box_0 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1002446457/5000000000 : ℝ)*x 0 + (2687570521/5000000000 : ℝ)*x 1 + (41993291/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1002446457/5000000000 : ℝ)^8415 ≤ (5978233104243/50000000000000 : ℝ)^6367 := by
    have hnat : (1002446457 : ℕ)^8415*50000000000000^6367 ≤ 5978233104243^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002446457 5000000000 5978233104243 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2687570521/5000000000 : ℝ)^8415 ≤ (22010882886903/50000000000000 : ℝ)^6367 := by
    have hnat : (2687570521 : ℕ)^8415*50000000000000^6367 ≤ 22010882886903^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687570521 5000000000 22010882886903 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41993291/78125000 : ℝ)^8415 ≤ (11005442000899/25000000000000 : ℝ)^6367 := by
    have hnat : (41993291 : ℕ)^8415*25000000000000^6367 ≤ 11005442000899^6367*78125000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41993291 78125000 11005442000899 25000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1002446457/5000000000 : ℝ), (2687570521/5000000000 : ℝ), (41993291/78125000 : ℝ)] ![(5978233104243/50000000000000 : ℝ), (22010882886903/50000000000000 : ℝ), (11005442000899/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1002446457/5000000000 : ℝ)|^8415 ≤ (5978233104243/50000000000000 : ℝ)^6367
        have hw : |(-1002446457/5000000000 : ℝ)|=(1002446457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2687570521/5000000000 : ℝ)|^8415 ≤ (22010882886903/50000000000000 : ℝ)^6367
        have hw : |(2687570521/5000000000 : ℝ)|=(2687570521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41993291/78125000 : ℝ)|^8415 ≤ (11005442000899/25000000000000 : ℝ)^6367
        have hw : |(41993291/78125000 : ℝ)|=(41993291/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_box_1 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5296652299/10000000000 : ℝ)*x 0 + (-527881529/2500000000 : ℝ)*x 1 + (5375141347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296652299/10000000000 : ℝ)^8415 ≤ (43174187685327/100000000000000 : ℝ)^6367 := by
    have hnat : (5296652299 : ℕ)^8415*100000000000000^6367 ≤ 43174187685327^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296652299 10000000000 43174187685327 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (527881529/2500000000 : ℝ)^8415 ≤ (12804043230091/100000000000000 : ℝ)^6367 := by
    have hnat : (527881529 : ℕ)^8415*100000000000000^6367 ≤ 12804043230091^6367*2500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527881529 2500000000 12804043230091 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375141347/10000000000 : ℝ)^8415 ≤ (8804353815039/20000000000000 : ℝ)^6367 := by
    have hnat : (5375141347 : ℕ)^8415*20000000000000^6367 ≤ 8804353815039^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375141347 10000000000 8804353815039 20000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296652299/10000000000 : ℝ), (-527881529/2500000000 : ℝ), (5375141347/10000000000 : ℝ)] ![(43174187685327/100000000000000 : ℝ), (12804043230091/100000000000000 : ℝ), (8804353815039/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296652299/10000000000 : ℝ)|^8415 ≤ (43174187685327/100000000000000 : ℝ)^6367
        have hw : |(5296652299/10000000000 : ℝ)|=(5296652299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-527881529/2500000000 : ℝ)|^8415 ≤ (12804043230091/100000000000000 : ℝ)^6367
        have hw : |(-527881529/2500000000 : ℝ)|=(527881529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375141347/10000000000 : ℝ)|^8415 ≤ (8804353815039/20000000000000 : ℝ)^6367
        have hw : |(5375141347/10000000000 : ℝ)|=(5375141347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_box_2 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5296652727/10000000000 : ℝ)*x 0 + (1075028211/2000000000 : ℝ)*x 1 + (-1055762967/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296652727/10000000000 : ℝ)^8415 ≤ (43174192296227/100000000000000 : ℝ)^6367 := by
    have hnat : (5296652727 : ℕ)^8415*100000000000000^6367 ≤ 43174192296227^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296652727 10000000000 43174192296227 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075028211/2000000000 : ℝ)^8415 ≤ (44021765914521/100000000000000 : ℝ)^6367 := by
    have hnat : (1075028211 : ℕ)^8415*100000000000000^6367 ≤ 44021765914521^6367*2000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075028211 2000000000 44021765914521 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1055762967/5000000000 : ℝ)^8415 ≤ (6402020885737/50000000000000 : ℝ)^6367 := by
    have hnat : (1055762967 : ℕ)^8415*50000000000000^6367 ≤ 6402020885737^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055762967 5000000000 6402020885737 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296652727/10000000000 : ℝ), (1075028211/2000000000 : ℝ), (-1055762967/5000000000 : ℝ)] ![(43174192296227/100000000000000 : ℝ), (44021765914521/100000000000000 : ℝ), (6402020885737/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296652727/10000000000 : ℝ)|^8415 ≤ (43174192296227/100000000000000 : ℝ)^6367
        have hw : |(5296652727/10000000000 : ℝ)|=(5296652727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1075028211/2000000000 : ℝ)|^8415 ≤ (44021765914521/100000000000000 : ℝ)^6367
        have hw : |(1075028211/2000000000 : ℝ)|=(1075028211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1055762967/5000000000 : ℝ)|^8415 ≤ (6402020885737/50000000000000 : ℝ)^6367
        have hw : |(-1055762967/5000000000 : ℝ)|=(1055762967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_box_3 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1115061611/2500000000 : ℝ)*x 0 + (1075554917/2500000000 : ℝ)*x 1 + (215110981/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1115061611/2500000000 : ℝ)^8415 ≤ (34401084414107/100000000000000 : ℝ)^6367 := by
    have hnat : (1115061611 : ℕ)^8415*100000000000000^6367 ≤ 34401084414107^6367*2500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115061611 2500000000 34401084414107 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075554917/2500000000 : ℝ)^8415 ≤ (16399729012167/50000000000000 : ℝ)^6367 := by
    have hnat : (1075554917 : ℕ)^8415*50000000000000^6367 ≤ 16399729012167^6367*2500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075554917 2500000000 16399729012167 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215110981/500000000 : ℝ)^8415 ≤ (819986438517/2500000000000 : ℝ)^6367 := by
    have hnat : (215110981 : ℕ)^8415*2500000000000^6367 ≤ 819986438517^6367*500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215110981 500000000 819986438517 2500000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1115061611/2500000000 : ℝ), (1075554917/2500000000 : ℝ), (215110981/500000000 : ℝ)] ![(34401084414107/100000000000000 : ℝ), (16399729012167/50000000000000 : ℝ), (819986438517/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1115061611/2500000000 : ℝ)|^8415 ≤ (34401084414107/100000000000000 : ℝ)^6367
        have hw : |(1115061611/2500000000 : ℝ)|=(1115061611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1075554917/2500000000 : ℝ)|^8415 ≤ (16399729012167/50000000000000 : ℝ)^6367
        have hw : |(1075554917/2500000000 : ℝ)|=(1075554917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215110981/500000000 : ℝ)|^8415 ≤ (819986438517/2500000000000 : ℝ)^6367
        have hw : |(215110981/500000000 : ℝ)|=(215110981/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_box_4 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-281863297/1250000000 : ℝ)*x 0 + (5282077929/10000000000 : ℝ)*x 1 + (1320519477/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (281863297/1250000000 : ℝ)^8415 ≤ (3491377252747/25000000000000 : ℝ)^6367 := by
    have hnat : (281863297 : ℕ)^8415*25000000000000^6367 ≤ 3491377252747^6367*1250000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281863297 1250000000 3491377252747 25000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5282077929/10000000000 : ℝ)^8415 ≤ (21508622800421/50000000000000 : ℝ)^6367 := by
    have hnat : (5282077929 : ℕ)^8415*50000000000000^6367 ≤ 21508622800421^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282077929 10000000000 21508622800421 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1320519477/2500000000 : ℝ)^8415 ≤ (43017245374807/100000000000000 : ℝ)^6367 := by
    have hnat : (1320519477 : ℕ)^8415*100000000000000^6367 ≤ 43017245374807^6367*2500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320519477 2500000000 43017245374807 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-281863297/1250000000 : ℝ), (5282077929/10000000000 : ℝ), (1320519477/2500000000 : ℝ)] ![(3491377252747/25000000000000 : ℝ), (21508622800421/50000000000000 : ℝ), (43017245374807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-281863297/1250000000 : ℝ)|^8415 ≤ (3491377252747/25000000000000 : ℝ)^6367
        have hw : |(-281863297/1250000000 : ℝ)|=(281863297/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5282077929/10000000000 : ℝ)|^8415 ≤ (21508622800421/50000000000000 : ℝ)^6367
        have hw : |(5282077929/10000000000 : ℝ)|=(5282077929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1320519477/2500000000 : ℝ)|^8415 ≤ (43017245374807/100000000000000 : ℝ)^6367
        have hw : |(1320519477/2500000000 : ℝ)|=(1320519477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_box_5 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2681142101/5000000000 : ℝ)*x 0 + (-2148363691/10000000000 : ℝ)*x 1 + (660259761/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681142101/5000000000 : ℝ)^8415 ≤ (43882653992057/100000000000000 : ℝ)^6367 := by
    have hnat : (2681142101 : ℕ)^8415*100000000000000^6367 ≤ 43882653992057^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681142101 5000000000 43882653992057 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2148363691/10000000000 : ℝ)^8415 ≤ (2620019736627/20000000000000 : ℝ)^6367 := by
    have hnat : (2148363691 : ℕ)^8415*20000000000000^6367 ≤ 2620019736627^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148363691 10000000000 2620019736627 20000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (660259761/1250000000 : ℝ)^8415 ≤ (43017247312253/100000000000000 : ℝ)^6367 := by
    have hnat : (660259761 : ℕ)^8415*100000000000000^6367 ≤ 43017247312253^6367*1250000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660259761 1250000000 43017247312253 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681142101/5000000000 : ℝ), (-2148363691/10000000000 : ℝ), (660259761/1250000000 : ℝ)] ![(43882653992057/100000000000000 : ℝ), (2620019736627/20000000000000 : ℝ), (43017247312253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681142101/5000000000 : ℝ)|^8415 ≤ (43882653992057/100000000000000 : ℝ)^6367
        have hw : |(2681142101/5000000000 : ℝ)|=(2681142101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2148363691/10000000000 : ℝ)|^8415 ≤ (2620019736627/20000000000000 : ℝ)^6367
        have hw : |(-2148363691/10000000000 : ℝ)|=(2148363691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(660259761/1250000000 : ℝ)|^8415 ≤ (43017247312253/100000000000000 : ℝ)^6367
        have hw : |(660259761/1250000000 : ℝ)|=(660259761/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_box_6 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5362284599/10000000000 : ℝ)*x 0 + (1056415547/2000000000 : ℝ)*x 1 + (-2148363629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362284599/10000000000 : ℝ)^8415 ≤ (21941329142983/50000000000000 : ℝ)^6367 := by
    have hnat : (5362284599 : ℕ)^8415*50000000000000^6367 ≤ 21941329142983^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362284599 10000000000 21941329142983 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056415547/2000000000 : ℝ)^8415 ≤ (21508621756353/50000000000000 : ℝ)^6367 := by
    have hnat : (1056415547 : ℕ)^8415*50000000000000^6367 ≤ 21508621756353^6367*2000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056415547 2000000000 21508621756353 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2148363629/10000000000 : ℝ)^8415 ≤ (818756136467/6250000000000 : ℝ)^6367 := by
    have hnat : (2148363629 : ℕ)^8415*6250000000000^6367 ≤ 818756136467^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148363629 10000000000 818756136467 6250000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362284599/10000000000 : ℝ), (1056415547/2000000000 : ℝ), (-2148363629/10000000000 : ℝ)] ![(21941329142983/50000000000000 : ℝ), (21508621756353/50000000000000 : ℝ), (818756136467/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362284599/10000000000 : ℝ)|^8415 ≤ (21941329142983/50000000000000 : ℝ)^6367
        have hw : |(5362284599/10000000000 : ℝ)|=(5362284599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056415547/2000000000 : ℝ)|^8415 ≤ (21508621756353/50000000000000 : ℝ)^6367
        have hw : |(1056415547/2000000000 : ℝ)|=(1056415547/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2148363629/10000000000 : ℝ)|^8415 ≤ (818756136467/6250000000000 : ℝ)^6367
        have hw : |(-2148363629/10000000000 : ℝ)|=(2148363629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_box_7 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (530801343/1250000000 : ℝ)*x 0 + (1102279291/2500000000 : ℝ)*x 1 + (1102279337/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530801343/1250000000 : ℝ)^8415 ≤ (6447659447803/20000000000000 : ℝ)^6367 := by
    have hnat : (530801343 : ℕ)^8415*20000000000000^6367 ≤ 6447659447803^6367*1250000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530801343 1250000000 6447659447803 20000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1102279291/2500000000 : ℝ)^8415 ≤ (8470212608923/25000000000000 : ℝ)^6367 := by
    have hnat : (1102279291 : ℕ)^8415*25000000000000^6367 ≤ 8470212608923^6367*2500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102279291 2500000000 8470212608923 25000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1102279337/2500000000 : ℝ)^8415 ≤ (33880852304393/100000000000000 : ℝ)^6367 := by
    have hnat : (1102279337 : ℕ)^8415*100000000000000^6367 ≤ 33880852304393^6367*2500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102279337 2500000000 33880852304393 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530801343/1250000000 : ℝ), (1102279291/2500000000 : ℝ), (1102279337/2500000000 : ℝ)] ![(6447659447803/20000000000000 : ℝ), (8470212608923/25000000000000 : ℝ), (33880852304393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530801343/1250000000 : ℝ)|^8415 ≤ (6447659447803/20000000000000 : ℝ)^6367
        have hw : |(530801343/1250000000 : ℝ)|=(530801343/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1102279291/2500000000 : ℝ)|^8415 ≤ (8470212608923/25000000000000 : ℝ)^6367
        have hw : |(1102279291/2500000000 : ℝ)|=(1102279291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1102279337/2500000000 : ℝ)|^8415 ≤ (33880852304393/100000000000000 : ℝ)^6367
        have hw : |(1102279337/2500000000 : ℝ)|=(1102279337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_box_8 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1101268621/5000000000 : ℝ)*x 0 + (326164753/625000000 : ℝ)*x 1 + (673094211/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1101268621/5000000000 : ℝ)^8415 ≤ (6769224417071/50000000000000 : ℝ)^6367 := by
    have hnat : (1101268621 : ℕ)^8415*50000000000000^6367 ≤ 6769224417071^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101268621 5000000000 6769224417071 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (326164753/625000000 : ℝ)^8415 ≤ (21167853004139/50000000000000 : ℝ)^6367 := by
    have hnat : (326164753 : ℕ)^8415*50000000000000^6367 ≤ 21167853004139^6367*625000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326164753 625000000 21167853004139 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673094211/1250000000 : ℝ)^8415 ≤ (4412584514431/10000000000000 : ℝ)^6367 := by
    have hnat : (673094211 : ℕ)^8415*10000000000000^6367 ≤ 4412584514431^6367*1250000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673094211 1250000000 4412584514431 10000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1101268621/5000000000 : ℝ), (326164753/625000000 : ℝ), (673094211/1250000000 : ℝ)] ![(6769224417071/50000000000000 : ℝ), (21167853004139/50000000000000 : ℝ), (4412584514431/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1101268621/5000000000 : ℝ)|^8415 ≤ (6769224417071/50000000000000 : ℝ)^6367
        have hw : |(-1101268621/5000000000 : ℝ)|=(1101268621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(326164753/625000000 : ℝ)|^8415 ≤ (21167853004139/50000000000000 : ℝ)^6367
        have hw : |(326164753/625000000 : ℝ)|=(326164753/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673094211/1250000000 : ℝ)|^8415 ≤ (4412584514431/10000000000000 : ℝ)^6367
        have hw : |(673094211/1250000000 : ℝ)|=(673094211/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_box_9 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2644935059/5000000000 : ℝ)*x 0 + (-2107653669/10000000000 : ℝ)*x 1 + (5384753717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644935059/5000000000 : ℝ)^8415 ≤ (10775284351333/25000000000000 : ℝ)^6367 := by
    have hnat : (2644935059 : ℕ)^8415*25000000000000^6367 ≤ 10775284351333^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644935059 5000000000 10775284351333 25000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2107653669/10000000000 : ℝ)^8415 ≤ (6386508562523/50000000000000 : ℝ)^6367 := by
    have hnat : (2107653669 : ℕ)^8415*50000000000000^6367 ≤ 6386508562523^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107653669 10000000000 6386508562523 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5384753717/10000000000 : ℝ)^8415 ≤ (44125845458393/100000000000000 : ℝ)^6367 := by
    have hnat : (5384753717 : ℕ)^8415*100000000000000^6367 ≤ 44125845458393^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384753717 10000000000 44125845458393 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644935059/5000000000 : ℝ), (-2107653669/10000000000 : ℝ), (5384753717/10000000000 : ℝ)] ![(10775284351333/25000000000000 : ℝ), (6386508562523/50000000000000 : ℝ), (44125845458393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644935059/5000000000 : ℝ)|^8415 ≤ (10775284351333/25000000000000 : ℝ)^6367
        have hw : |(2644935059/5000000000 : ℝ)|=(2644935059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2107653669/10000000000 : ℝ)|^8415 ≤ (6386508562523/50000000000000 : ℝ)^6367
        have hw : |(-2107653669/10000000000 : ℝ)|=(2107653669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5384753717/10000000000 : ℝ)|^8415 ≤ (44125845458393/100000000000000 : ℝ)^6367
        have hw : |(5384753717/10000000000 : ℝ)|=(5384753717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_box_10 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5289870133/10000000000 : ℝ)*x 0 + (2692376839/5000000000 : ℝ)*x 1 + (-2107653701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289870133/10000000000 : ℝ)^8415 ≤ (21550568783431/50000000000000 : ℝ)^6367 := by
    have hnat : (5289870133 : ℕ)^8415*50000000000000^6367 ≤ 21550568783431^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289870133 10000000000 21550568783431 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2692376839/5000000000 : ℝ)^8415 ≤ (8825169007201/20000000000000 : ℝ)^6367 := by
    have hnat : (2692376839 : ℕ)^8415*20000000000000^6367 ≤ 8825169007201^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692376839 5000000000 8825169007201 20000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2107653701/10000000000 : ℝ)^8415 ≤ (2554603476271/20000000000000 : ℝ)^6367 := by
    have hnat : (2107653701 : ℕ)^8415*20000000000000^6367 ≤ 2554603476271^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107653701 10000000000 2554603476271 20000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289870133/10000000000 : ℝ), (2692376839/5000000000 : ℝ), (-2107653701/10000000000 : ℝ)] ![(21550568783431/50000000000000 : ℝ), (8825169007201/20000000000000 : ℝ), (2554603476271/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289870133/10000000000 : ℝ)|^8415 ≤ (21550568783431/50000000000000 : ℝ)^6367
        have hw : |(5289870133/10000000000 : ℝ)|=(5289870133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2692376839/5000000000 : ℝ)|^8415 ≤ (8825169007201/20000000000000 : ℝ)^6367
        have hw : |(2692376839/5000000000 : ℝ)|=(2692376839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2107653701/10000000000 : ℝ)|^8415 ≤ (2554603476271/20000000000000 : ℝ)^6367
        have hw : |(-2107653701/10000000000 : ℝ)|=(2107653701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_box_11 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4482060787/10000000000 : ℝ)*x 0 + (2145585983/5000000000 : ℝ)*x 1 + (4291171919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4482060787/10000000000 : ℝ)^8415 ≤ (34623628360883/100000000000000 : ℝ)^6367 := by
    have hnat : (4482060787 : ℕ)^8415*100000000000000^6367 ≤ 34623628360883^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4482060787 10000000000 34623628360883 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2145585983/5000000000 : ℝ)^8415 ≤ (6537637209431/20000000000000 : ℝ)^6367 := by
    have hnat : (2145585983 : ℕ)^8415*20000000000000^6367 ≤ 6537637209431^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145585983 5000000000 6537637209431 20000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4291171919/10000000000 : ℝ)^8415 ≤ (32688185573969/100000000000000 : ℝ)^6367 := by
    have hnat : (4291171919 : ℕ)^8415*100000000000000^6367 ≤ 32688185573969^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4291171919 10000000000 32688185573969 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4482060787/10000000000 : ℝ), (2145585983/5000000000 : ℝ), (4291171919/10000000000 : ℝ)] ![(34623628360883/100000000000000 : ℝ), (6537637209431/20000000000000 : ℝ), (32688185573969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4482060787/10000000000 : ℝ)|^8415 ≤ (34623628360883/100000000000000 : ℝ)^6367
        have hw : |(4482060787/10000000000 : ℝ)|=(4482060787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2145585983/5000000000 : ℝ)|^8415 ≤ (6537637209431/20000000000000 : ℝ)^6367
        have hw : |(2145585983/5000000000 : ℝ)|=(2145585983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4291171919/10000000000 : ℝ)|^8415 ≤ (32688185573969/100000000000000 : ℝ)^6367
        have hw : |(4291171919/10000000000 : ℝ)|=(4291171919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_box_12 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-514383283/2500000000 : ℝ)*x 0 + (1087472247/2000000000 : ℝ)*x 1 + (2637003059/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (514383283/2500000000 : ℝ)^8415 ≤ (6186556444153/50000000000000 : ℝ)^6367 := by
    have hnat : (514383283 : ℕ)^8415*50000000000000^6367 ≤ 6186556444153^6367*2500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514383283 2500000000 6186556444153 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087472247/2000000000 : ℝ)^8415 ≤ (44696501778273/100000000000000 : ℝ)^6367 := by
    have hnat : (1087472247 : ℕ)^8415*100000000000000^6367 ≤ 44696501778273^6367*2000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087472247 2000000000 44696501778273 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2637003059/5000000000 : ℝ)^8415 ≤ (42930385313357/100000000000000 : ℝ)^6367 := by
    have hnat : (2637003059 : ℕ)^8415*100000000000000^6367 ≤ 42930385313357^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637003059 5000000000 42930385313357 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-514383283/2500000000 : ℝ), (1087472247/2000000000 : ℝ), (2637003059/5000000000 : ℝ)] ![(6186556444153/50000000000000 : ℝ), (44696501778273/100000000000000 : ℝ), (42930385313357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-514383283/2500000000 : ℝ)|^8415 ≤ (6186556444153/50000000000000 : ℝ)^6367
        have hw : |(-514383283/2500000000 : ℝ)|=(514383283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1087472247/2000000000 : ℝ)|^8415 ≤ (44696501778273/100000000000000 : ℝ)^6367
        have hw : |(1087472247/2000000000 : ℝ)|=(1087472247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2637003059/5000000000 : ℝ)|^8415 ≤ (42930385313357/100000000000000 : ℝ)^6367
        have hw : |(2637003059/5000000000 : ℝ)|=(2637003059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_box_13 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2683987231/5000000000 : ℝ)*x 0 + (-537875659/2500000000 : ℝ)*x 1 + (5274006423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2683987231/5000000000 : ℝ)^8415 ≤ (43944209728851/100000000000000 : ℝ)^6367 := by
    have hnat : (2683987231 : ℕ)^8415*100000000000000^6367 ≤ 43944209728851^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2683987231 5000000000 43944209728851 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (537875659/2500000000 : ℝ)^8415 ≤ (6562700833751/50000000000000 : ℝ)^6367 := by
    have hnat : (537875659 : ℕ)^8415*50000000000000^6367 ≤ 6562700833751^6367*2500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537875659 2500000000 6562700833751 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5274006423/10000000000 : ℝ)^8415 ≤ (42930388594637/100000000000000 : ℝ)^6367 := by
    have hnat : (5274006423 : ℕ)^8415*100000000000000^6367 ≤ 42930388594637^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274006423 10000000000 42930388594637 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2683987231/5000000000 : ℝ), (-537875659/2500000000 : ℝ), (5274006423/10000000000 : ℝ)] ![(43944209728851/100000000000000 : ℝ), (6562700833751/50000000000000 : ℝ), (42930388594637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2683987231/5000000000 : ℝ)|^8415 ≤ (43944209728851/100000000000000 : ℝ)^6367
        have hw : |(2683987231/5000000000 : ℝ)|=(2683987231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-537875659/2500000000 : ℝ)|^8415 ≤ (6562700833751/50000000000000 : ℝ)^6367
        have hw : |(-537875659/2500000000 : ℝ)|=(537875659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5274006423/10000000000 : ℝ)|^8415 ≤ (42930388594637/100000000000000 : ℝ)^6367
        have hw : |(5274006423/10000000000 : ℝ)|=(5274006423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_box_14 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1341993753/2500000000 : ℝ)*x 0 + (1318501547/2500000000 : ℝ)*x 1 + (-215150221/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1341993753/2500000000 : ℝ)^8415 ≤ (43944215679621/100000000000000 : ℝ)^6367 := by
    have hnat : (1341993753 : ℕ)^8415*100000000000000^6367 ≤ 43944215679621^6367*2500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1341993753 2500000000 43944215679621 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1318501547/2500000000 : ℝ)^8415 ≤ (21465193033219/50000000000000 : ℝ)^6367 := by
    have hnat : (1318501547 : ℕ)^8415*50000000000000^6367 ≤ 21465193033219^6367*2500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318501547 2500000000 21465193033219 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215150221/1000000000 : ℝ)^8415 ≤ (13125398232717/100000000000000 : ℝ)^6367 := by
    have hnat : (215150221 : ℕ)^8415*100000000000000^6367 ≤ 13125398232717^6367*1000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215150221 1000000000 13125398232717 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1341993753/2500000000 : ℝ), (1318501547/2500000000 : ℝ), (-215150221/1000000000 : ℝ)] ![(43944215679621/100000000000000 : ℝ), (21465193033219/50000000000000 : ℝ), (13125398232717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1341993753/2500000000 : ℝ)|^8415 ≤ (43944215679621/100000000000000 : ℝ)^6367
        have hw : |(1341993753/2500000000 : ℝ)|=(1341993753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1318501547/2500000000 : ℝ)|^8415 ≤ (21465193033219/50000000000000 : ℝ)^6367
        have hw : |(1318501547/2500000000 : ℝ)|=(1318501547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-215150221/1000000000 : ℝ)|^8415 ≤ (13125398232717/100000000000000 : ℝ)^6367
        have hw : |(-215150221/1000000000 : ℝ)|=(215150221/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_box_15 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (845526281/2000000000 : ℝ)*x 0 + (4418384809/10000000000 : ℝ)*x 1 + (4418383813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (845526281/2000000000 : ℝ)^8415 ≤ (4006250194941/12500000000000 : ℝ)^6367 := by
    have hnat : (845526281 : ℕ)^8415*12500000000000^6367 ≤ 4006250194941^6367*2000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845526281 2000000000 4006250194941 12500000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4418384809/10000000000 : ℝ)^8415 ≤ (16987502138471/50000000000000 : ℝ)^6367 := by
    have hnat : (4418384809 : ℕ)^8415*50000000000000^6367 ≤ 16987502138471^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4418384809 10000000000 16987502138471 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4418383813/10000000000 : ℝ)^8415 ≤ (33974994154749/100000000000000 : ℝ)^6367 := by
    have hnat : (4418383813 : ℕ)^8415*100000000000000^6367 ≤ 33974994154749^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4418383813 10000000000 33974994154749 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(845526281/2000000000 : ℝ), (4418384809/10000000000 : ℝ), (4418383813/10000000000 : ℝ)] ![(4006250194941/12500000000000 : ℝ), (16987502138471/50000000000000 : ℝ), (33974994154749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(845526281/2000000000 : ℝ)|^8415 ≤ (4006250194941/12500000000000 : ℝ)^6367
        have hw : |(845526281/2000000000 : ℝ)|=(845526281/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4418384809/10000000000 : ℝ)|^8415 ≤ (16987502138471/50000000000000 : ℝ)^6367
        have hw : |(4418384809/10000000000 : ℝ)|=(4418384809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4418383813/10000000000 : ℝ)|^8415 ≤ (33974994154749/100000000000000 : ℝ)^6367
        have hw : |(4418383813/10000000000 : ℝ)|=(4418383813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1222_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75518489/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2291/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62243/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59361/100000 : ℝ) ∧ (1601/2000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41651/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14093/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2291/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14093/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2291/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14093/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2291/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14093/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2291/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14093/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2291/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14093/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2291/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2291/20000 : ℝ) ^ (4207/1024 : ℝ) ≤ (13613723089077309/100000000000000000000 : ℝ) := by
    have hpowers : (2291/20000 : ℝ)^4207 ≤ (13613723089077309/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2291 : ℕ)^4207*100000000000000000000^1024 ≤ 13613723089077309^1024*20000^4207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2291 20000 13613723089077309 100000000000000000000 4207 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2291/20000 : ℝ)) (X := (13613723089077309/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14093/100000 : ℝ) ^ (4207/1024 : ℝ) ≤ (31898268664287787/100000000000000000000 : ℝ) := by
    have hpowers : (14093/100000 : ℝ)^4207 ≤ (31898268664287787/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14093 : ℕ)^4207*100000000000000000000^1024 ≤ 31898268664287787^1024*100000^4207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14093 100000 31898268664287787 100000000000000000000 4207 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14093/100000 : ℝ)) (X := (31898268664287787/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013613723089077309/50000000000000000000 : ℝ) ≤ (5000331329136983/5000000000000000 : ℝ) ^ (4207/1024 : ℝ) := by
    have hpowers : (50013613723089077309/50000000000000000000 : ℝ)^1024 ≤ (5000331329136983/5000000000000000 : ℝ)^4207 := by
      have hnat : (50013613723089077309 : ℕ)^1024*5000000000000000^4207 ≤ 5000331329136983^4207*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013613723089077309 50000000000000000000 5000331329136983 5000000000000000 1024 4207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000331329136983/5000000000000000 : ℝ)) (X := (50013613723089077309/50000000000000000000 : ℝ)) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505688998969170637/12500000000000000000 : ℝ) ≤ (10001107588728029/10000000000000000 : ℝ) ^ (4207/1024 : ℝ) := by
    have hpowers : (12505688998969170637/12500000000000000000 : ℝ)^1024 ≤ (10001107588728029/10000000000000000 : ℝ)^4207 := by
      have hnat : (12505688998969170637 : ℕ)^1024*10000000000000000^4207 ≤ 10001107588728029^4207*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505688998969170637 12500000000000000000 10001107588728029 10000000000000000 1024 4207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001107588728029/10000000000000000 : ℝ)) (X := (12505688998969170637/12500000000000000000 : ℝ)) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031898268664287787/50000000000000000000 : ℝ) ≤ (2500388129795523/2500000000000000 : ℝ) ^ (4207/1024 : ℝ) := by
    have hpowers : (50031898268664287787/50000000000000000000 : ℝ)^1024 ≤ (2500388129795523/2500000000000000 : ℝ)^4207 := by
      have hnat : (50031898268664287787 : ℕ)^1024*2500000000000000^4207 ≤ 2500388129795523^4207*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031898268664287787 50000000000000000000 2500388129795523 2500000000000000 1024 4207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500388129795523/2500000000000000 : ℝ)) (X := (50031898268664287787/50000000000000000000 : ℝ)) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13613723089077309/100000000000000000000 : ℝ) ≤ ((13185777367912069489/13190000000000000000 : ℝ)+2*(444930454063/263800000000000 : ℝ)*(2291/20000 : ℝ))^(4207/1024 : ℝ) := by
    rw [show (13185777367912069489/13190000000000000000 : ℝ)+2*(444930454063/263800000000000 : ℝ)*(2291/20000 : ℝ)=(5000331329136983/5000000000000000 : ℝ) by norm_num, show 1+2*(13613723089077309/100000000000000000000 : ℝ)=(50013613723089077309/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31898268664287787/100000000000000000000 : ℝ)+(13613723089077309/100000000000000000000 : ℝ) ≤ ((13185777367912069489/13190000000000000000 : ℝ)+(444930454063/263800000000000 : ℝ)*((14093/100000 : ℝ)+(2291/20000 : ℝ)))^(4207/1024 : ℝ) := by
    rw [show (13185777367912069489/13190000000000000000 : ℝ)+(444930454063/263800000000000 : ℝ)*((14093/100000 : ℝ)+(2291/20000 : ℝ))=(10001107588728029/10000000000000000 : ℝ) by norm_num, show 1+(31898268664287787/100000000000000000000 : ℝ)+(13613723089077309/100000000000000000000 : ℝ)=(12505688998969170637/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31898268664287787/100000000000000000000 : ℝ) ≤ ((13185777367912069489/13190000000000000000 : ℝ)+2*(444930454063/263800000000000 : ℝ)*(14093/100000 : ℝ))^(4207/1024 : ℝ) := by
    rw [show (13185777367912069489/13190000000000000000 : ℝ)+2*(444930454063/263800000000000 : ℝ)*(14093/100000 : ℝ)=(2500388129795523/2500000000000000 : ℝ) by norm_num, show 1+2*(31898268664287787/100000000000000000000 : ℝ)=(50031898268664287787/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13185777367912069489/13190000000000000000 : ℝ)*(X 1 0+X 2 0)+(444930454063/263800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4207/1024 : ℝ)) (lo := (2291/20000 : ℝ)) (hi := (14093/100000 : ℝ)) (c := (13185777367912069489/13190000000000000000 : ℝ)) (alpha := (444930454063/263800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13185777367912069489/13190000000000000000 : ℝ)*(X 0 1+X 2 1)+(444930454063/263800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4207/1024 : ℝ)) (lo := (2291/20000 : ℝ)) (hi := (14093/100000 : ℝ)) (c := (13185777367912069489/13190000000000000000 : ℝ)) (alpha := (444930454063/263800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13185777367912069489/13190000000000000000 : ℝ)*(X 0 2+X 1 2)+(444930454063/263800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4207/1024 : ℝ)) (lo := (2291/20000 : ℝ)) (hi := (14093/100000 : ℝ)) (c := (13185777367912069489/13190000000000000000 : ℝ)) (alpha := (444930454063/263800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1002446457/5000000000 : ℝ)*X 0 0+(2687570521/5000000000 : ℝ)*X 0 1+(41993291/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5296652299/10000000000 : ℝ)*X 1 0+(-527881529/2500000000 : ℝ)*X 1 1+(5375141347/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5296652727/10000000000 : ℝ)*X 2 0+(1075028211/2000000000 : ℝ)*X 2 1+(-1055762967/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1115061611/2500000000 : ℝ)*X 0 0+(1075554917/2500000000 : ℝ)*X 0 1+(215110981/500000000 : ℝ)*X 0 2+(1115061611/2500000000 : ℝ)*X 1 0+(1075554917/2500000000 : ℝ)*X 1 1+(215110981/500000000 : ℝ)*X 1 2+(1115061611/2500000000 : ℝ)*X 2 0+(1075554917/2500000000 : ℝ)*X 2 1+(215110981/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-281863297/1250000000 : ℝ)*X 0 0+(5282077929/10000000000 : ℝ)*X 0 1+(1320519477/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2681142101/5000000000 : ℝ)*X 1 0+(-2148363691/10000000000 : ℝ)*X 1 1+(660259761/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5362284599/10000000000 : ℝ)*X 2 0+(1056415547/2000000000 : ℝ)*X 2 1+(-2148363629/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((530801343/1250000000 : ℝ)*X 0 0+(1102279291/2500000000 : ℝ)*X 0 1+(1102279337/2500000000 : ℝ)*X 0 2+(530801343/1250000000 : ℝ)*X 1 0+(1102279291/2500000000 : ℝ)*X 1 1+(1102279337/2500000000 : ℝ)*X 1 2+(530801343/1250000000 : ℝ)*X 2 0+(1102279291/2500000000 : ℝ)*X 2 1+(1102279337/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1101268621/5000000000 : ℝ)*X 0 0+(326164753/625000000 : ℝ)*X 0 1+(673094211/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2644935059/5000000000 : ℝ)*X 1 0+(-2107653669/10000000000 : ℝ)*X 1 1+(5384753717/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5289870133/10000000000 : ℝ)*X 2 0+(2692376839/5000000000 : ℝ)*X 2 1+(-2107653701/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4482060787/10000000000 : ℝ)*X 0 0+(2145585983/5000000000 : ℝ)*X 0 1+(4291171919/10000000000 : ℝ)*X 0 2+(4482060787/10000000000 : ℝ)*X 1 0+(2145585983/5000000000 : ℝ)*X 1 1+(4291171919/10000000000 : ℝ)*X 1 2+(4482060787/10000000000 : ℝ)*X 2 0+(2145585983/5000000000 : ℝ)*X 2 1+(4291171919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-514383283/2500000000 : ℝ)*X 0 0+(1087472247/2000000000 : ℝ)*X 0 1+(2637003059/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2683987231/5000000000 : ℝ)*X 1 0+(-537875659/2500000000 : ℝ)*X 1 1+(5274006423/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1341993753/2500000000 : ℝ)*X 2 0+(1318501547/2500000000 : ℝ)*X 2 1+(-215150221/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((845526281/2000000000 : ℝ)*X 0 0+(4418384809/10000000000 : ℝ)*X 0 1+(4418383813/10000000000 : ℝ)*X 0 2+(845526281/2000000000 : ℝ)*X 1 0+(4418384809/10000000000 : ℝ)*X 1 1+(4418383813/10000000000 : ℝ)*X 1 2+(845526281/2000000000 : ℝ)*X 2 0+(4418384809/10000000000 : ℝ)*X 2 1+(4418383813/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62243/100000 : ℝ) ≤ (-205237751969205621393105483374013/329750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15765703/20000000000000 : ℝ)*(upper0) + (27789707/100000000000000 : ℝ)*(lower1) + (66432043/50000000000000 : ℝ)*(lower2) + (924203/50000000000000 : ℝ)*(lower3) + (8784337/50000000000000 : ℝ)*(upper5) + (3986831864046439/100000000000000 : ℝ)*(major0) + (3986831864046439/100000000000000 : ℝ)*(major1) + (3986831864046439/100000000000000 : ℝ)*(major2) + (572496143/12500000000000 : ℝ)*(sp2) + (1338692735816743/25000000000000 : ℝ)*(sp4) + (167333864667377/3125000000000 : ℝ)*(sp5) + (1338691590824457/25000000000000 : ℝ)*(sp6) + (659909897039657/25000000000000 : ℝ)*(sp7) + (21818477727/25000000000000 : ℝ)*(sp13) + (659909897039657/25000000000000 : ℝ)*(f.failure) + (1338692735816743/25000000000000 : ℝ)*(f.sum) + (76616801057257/13190000000000000000000000000 : ℝ)*base65 + (4561982016053849671/1319000000000000000000000000000000 : ℝ)*base67 + (1187477292393849671/1319000000000000000000000000000000 : ℝ)*base69 + (2727939323409849671/1319000000000000000000000000000000 : ℝ)*base71 + (678772227188457/13190000000000000000000000000 : ℝ)*base73 + (17412716380733849671/1319000000000000000000000000000000 : ℝ)*base75 + (12533779993874150329/1319000000000000000000000000000000 : ℝ)*base78 + (29564411145725849671/1319000000000000000000000000000000 : ℝ)*base79 + (1003049235118817/13190000000000000000000000000 : ℝ)*base81 + (17781727/1250000000000000000000 : ℝ)*base90 + (17781727/1250000000000000000000 : ℝ)*base92 + (17781727/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59361/100000 : ℝ) ≤ (7830088522079211954937667139/13190000000000000000000000000 : ℝ) := by norm_num
    linear_combination (36110127/100000000000000 : ℝ)*(lower0) + (80454389/100000000000000 : ℝ)*(lower1) + (180521163/100000000000000 : ℝ)*(lower2) + (6973321/10000000000000 : ℝ)*(lower3) + (4052319207887421/100000000000000 : ℝ)*(major0) + (4052319207887421/100000000000000 : ℝ)*(major1) + (4052319207887421/100000000000000 : ℝ)*(major2) + (5401852402003667/100000000000000 : ℝ)*(sp0) + (2700923903792427/50000000000000 : ℝ)*(sp1) + (675227767760597/12500000000000 : ℝ)*(sp2) + (670748677105453/25000000000000 : ℝ)*(sp3) + (4594418813/100000000000000 : ℝ)*(sp5) + (3363671117/100000000000000 : ℝ)*(sp7) + (7564979723/25000000000000 : ℝ)*(sp10) + (2682998072092929/100000000000000 : ℝ)*(f.failure) + (5401852402003667/100000000000000 : ℝ)*(f.sum) + (87305049520697/13190000000000000000000000000 : ℝ)*base66 + (6175399010224852131/1319000000000000000000000000000000 : ℝ)*base68 + (15650761464449147869/1319000000000000000000000000000000 : ℝ)*base69 + (2170655887705147869/1319000000000000000000000000000000 : ℝ)*base71 + (43419054903307/13190000000000000000000000000 : ℝ)*base74 + (2659044800795147869/1319000000000000000000000000000000 : ℝ)*base75 + (9912261532198852131/1319000000000000000000000000000000 : ℝ)*base78 + (17941620871222852131/1319000000000000000000000000000000 : ℝ)*base80 + (61037774076323/13190000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (15664281/5000000000000000000000 : ℝ)*base89 + (15664281/5000000000000000000000 : ℝ)*base91 + (15664281/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (1601/2000 : ℝ) ≤ (263971808701591350689924055241707/329750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1623651/100000000000000 : ℝ)*(upper0) + (4205627/25000000000000 : ℝ)*(upper1) + (131257/781250000000 : ℝ)*(upper2) + (1446229/20000000000000 : ℝ)*(upper3) + (6745807/100000000000000 : ℝ)*(upper4) + (2259685780711721/50000000000000 : ℝ)*(major0) + (2259685780711721/50000000000000 : ℝ)*(major1) + (2259685780711721/50000000000000 : ℝ)*(major2) + (28139649199/100000000000000 : ℝ)*(sp1) + (66948941/800000000000 : ℝ)*(sp3) + (1504957637192891/25000000000000 : ℝ)*(sp8) + (1504950602280591/25000000000000 : ℝ)*(sp9) + (1504957637192891/25000000000000 : ℝ)*(sp10) + (59844403424389/2000000000000 : ℝ)*(sp11) + (1496114269918537/50000000000000 : ℝ)*(f.failure) + (1504957637192891/25000000000000 : ℝ)*(f.sum) + (36652691984033/6595000000000000000000000000 : ℝ)*base65 + (10426792794665930569/659500000000000000000000000000000 : ℝ)*base67 + (7344113205529069431/659500000000000000000000000000000 : ℝ)*base70 + (52529844033121430569/659500000000000000000000000000000 : ℝ)*base71 + (75071596724577/6595000000000000000000000000 : ℝ)*base74 + (1249429696464569431/659500000000000000000000000000000 : ℝ)*base76 + (52579498875539069431/659500000000000000000000000000000 : ℝ)*base78 + (17023624059874069431/659500000000000000000000000000000 : ℝ)*base80 + (13819980811747/6595000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (17330593/2500000000000000000000 : ℝ)*base89 + (17330593/2500000000000000000000 : ℝ)*base91 + (17330593/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-41651/50000 : ℝ) ≤ (-109871929732550771683274121286209/131900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (188871087/100000000000000 : ℝ)*(lower0) + (7919563/25000000000000 : ℝ)*(upper1) + (13467519/4000000000000 : ℝ)*(lower2) + (218065177/100000000000000 : ℝ)*(upper3) + (399063413/100000000000000 : ℝ)*(upper5) + (910947804552827/20000000000000 : ℝ)*(major0) + (910947804552827/20000000000000 : ℝ)*(major1) + (910947804552827/20000000000000 : ℝ)*(major2) + (199375259/50000000000000 : ℝ)*(sp4) + (228768822737/100000000000000 : ℝ)*(sp7) + (191299973547111/3125000000000 : ℝ)*(sp12) + (6121599552258071/100000000000000 : ℝ)*(sp13) + (6121599552258071/100000000000000 : ℝ)*(sp14) + (3015416196454663/100000000000000 : ℝ)*(sp15) + (15078224826387/500000000000 : ℝ)*(f.failure) + (6121599552258071/100000000000000 : ℝ)*(f.sum) + (124339826517/2638000000000000000000000000 : ℝ)*base66 + (3730419731392154597/263800000000000000000000000000000 : ℝ)*base68 + (2351189908895445403/263800000000000000000000000000000 : ℝ)*base69 + (2843628093949445403/263800000000000000000000000000000 : ℝ)*base71 + (18168251591699/2638000000000000000000000000 : ℝ)*base73 + (5445819649014045403/263800000000000000000000000000000 : ℝ)*base75 + (1856504572559445403/263800000000000000000000000000000 : ℝ)*base77 + (5840102038694954597/263800000000000000000000000000000 : ℝ)*base80 + (15381263930871/2638000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (180757/25000000000000000000 : ℝ)*base90 + (180757/25000000000000000000 : ℝ)*base92 + (180757/25000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1222_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75518489/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2291/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62243/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59361/100000 : ℝ) else (1601/2000 : ℝ) ≤ X j i ∧ X j i ≤ (41651/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1222_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1222_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75518489/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2291/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62243/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59361/100000 : ℝ) else (1601/2000 : ℝ) ≤ X j i ∧ X j i ≤ (41651/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1222_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75518489/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2291/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62243/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59361/100000 : ℝ) else (1601/2000 : ℝ) ≤ X j i ∧ X j i ≤ (41651/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1222_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

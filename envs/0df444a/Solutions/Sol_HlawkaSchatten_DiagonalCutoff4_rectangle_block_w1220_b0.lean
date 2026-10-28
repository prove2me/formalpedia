-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1220_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:10:33.527577+00:00
-- url     : https://prove2.me/submissions/dfed20b3-a5fb-44b2-824e-711a24e3b1c3

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
theorem support_rectangle_w1220_s0_0 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1867367353/10000000000 : ℝ)*x 0 + (6036477493/10000000000 : ℝ)*x 1 + (4790257199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1867367353/10000000000 : ℝ)^8413 ≤ (1088280693661/10000000000000 : ℝ)^6365 := by
    have hnat : (1867367353 : ℕ)^8413*10000000000000^6365 ≤ 1088280693661^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1867367353 10000000000 1088280693661 10000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6036477493/10000000000 : ℝ)^8413 ≤ (2052620141917/4000000000000 : ℝ)^6365 := by
    have hnat : (6036477493 : ℕ)^8413*4000000000000^6365 ≤ 2052620141917^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6036477493 10000000000 2052620141917 4000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4790257199/10000000000 : ℝ)^8413 ≤ (37801689506907/100000000000000 : ℝ)^6365 := by
    have hnat : (4790257199 : ℕ)^8413*100000000000000^6365 ≤ 37801689506907^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4790257199 10000000000 37801689506907 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1867367353/10000000000 : ℝ), (6036477493/10000000000 : ℝ), (4790257199/10000000000 : ℝ)] ![(1088280693661/10000000000000 : ℝ), (2052620141917/4000000000000 : ℝ), (37801689506907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1867367353/10000000000 : ℝ)|^8413 ≤ (1088280693661/10000000000000 : ℝ)^6365
        have hw : |(-1867367353/10000000000 : ℝ)|=(1867367353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6036477493/10000000000 : ℝ)|^8413 ≤ (2052620141917/4000000000000 : ℝ)^6365
        have hw : |(6036477493/10000000000 : ℝ)|=(6036477493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4790257199/10000000000 : ℝ)|^8413 ≤ (37801689506907/100000000000000 : ℝ)^6365
        have hw : |(4790257199/10000000000 : ℝ)|=(4790257199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s0_1 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (110247979/200000000 : ℝ)*x 0 + (-645099769/2500000000 : ℝ)*x 1 + (4790257161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (110247979/200000000 : ℝ)^8413 ≤ (568885044401/1250000000000 : ℝ)^6365 := by
    have hnat : (110247979 : ℕ)^8413*1250000000000^6365 ≤ 568885044401^6365*200000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110247979 200000000 568885044401 1250000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (645099769/2500000000 : ℝ)^8413 ≤ (8343753661871/50000000000000 : ℝ)^6365 := by
    have hnat : (645099769 : ℕ)^8413*50000000000000^6365 ≤ 8343753661871^6365*2500000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      645099769 2500000000 8343753661871 50000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4790257161/10000000000 : ℝ)^8413 ≤ (9450422277637/25000000000000 : ℝ)^6365 := by
    have hnat : (4790257161 : ℕ)^8413*25000000000000^6365 ≤ 9450422277637^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4790257161 10000000000 9450422277637 25000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(110247979/200000000 : ℝ), (-645099769/2500000000 : ℝ), (4790257161/10000000000 : ℝ)] ![(568885044401/1250000000000 : ℝ), (8343753661871/50000000000000 : ℝ), (9450422277637/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(110247979/200000000 : ℝ)|^8413 ≤ (568885044401/1250000000000 : ℝ)^6365
        have hw : |(110247979/200000000 : ℝ)|=(110247979/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-645099769/2500000000 : ℝ)|^8413 ≤ (8343753661871/50000000000000 : ℝ)^6365
        have hw : |(-645099769/2500000000 : ℝ)|=(645099769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4790257161/10000000000 : ℝ)|^8413 ≤ (9450422277637/25000000000000 : ℝ)^6365
        have hw : |(4790257161/10000000000 : ℝ)|=(4790257161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s0_2 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2756199461/5000000000 : ℝ)*x 0 + (1197564299/2500000000 : ℝ)*x 1 + (-2580399069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2756199461/5000000000 : ℝ)^8413 ≤ (45510803246529/100000000000000 : ℝ)^6365 := by
    have hnat : (2756199461 : ℕ)^8413*100000000000000^6365 ≤ 45510803246529^6365*5000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2756199461 5000000000 45510803246529 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1197564299/2500000000 : ℝ)^8413 ≤ (7560337895123/20000000000000 : ℝ)^6365 := by
    have hnat : (1197564299 : ℕ)^8413*20000000000000^6365 ≤ 7560337895123^6365*2500000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1197564299 2500000000 7560337895123 20000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2580399069/10000000000 : ℝ)^8413 ≤ (16687507263907/100000000000000 : ℝ)^6365 := by
    have hnat : (2580399069 : ℕ)^8413*100000000000000^6365 ≤ 16687507263907^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2580399069 10000000000 16687507263907 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2756199461/5000000000 : ℝ), (1197564299/2500000000 : ℝ), (-2580399069/10000000000 : ℝ)] ![(45510803246529/100000000000000 : ℝ), (7560337895123/20000000000000 : ℝ), (16687507263907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2756199461/5000000000 : ℝ)|^8413 ≤ (45510803246529/100000000000000 : ℝ)^6365
        have hw : |(2756199461/5000000000 : ℝ)|=(2756199461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1197564299/2500000000 : ℝ)|^8413 ≤ (7560337895123/20000000000000 : ℝ)^6365
        have hw : |(1197564299/2500000000 : ℝ)|=(1197564299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2580399069/10000000000 : ℝ)|^8413 ≤ (16687507263907/100000000000000 : ℝ)^6365
        have hw : |(-2580399069/10000000000 : ℝ)|=(2580399069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s0_3 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (838950979/2000000000 : ℝ)*x 0 + (155886853/500000000 : ℝ)*x 1 + (704381013/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (838950979/2000000000 : ℝ)^8413 ≤ (31718219775913/100000000000000 : ℝ)^6365 := by
    have hnat : (838950979 : ℕ)^8413*100000000000000^6365 ≤ 31718219775913^6365*2000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      838950979 2000000000 31718219775913 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (155886853/500000000 : ℝ)^8413 ≤ (21427794320983/100000000000000 : ℝ)^6365 := by
    have hnat : (155886853 : ℕ)^8413*100000000000000^6365 ≤ 21427794320983^6365*500000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155886853 500000000 21427794320983 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (704381013/1250000000 : ℝ)^8413 ≤ (46853985890221/100000000000000 : ℝ)^6365 := by
    have hnat : (704381013 : ℕ)^8413*100000000000000^6365 ≤ 46853985890221^6365*1250000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      704381013 1250000000 46853985890221 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(838950979/2000000000 : ℝ), (155886853/500000000 : ℝ), (704381013/1250000000 : ℝ)] ![(31718219775913/100000000000000 : ℝ), (21427794320983/100000000000000 : ℝ), (46853985890221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(838950979/2000000000 : ℝ)|^8413 ≤ (31718219775913/100000000000000 : ℝ)^6365
        have hw : |(838950979/2000000000 : ℝ)|=(838950979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(155886853/500000000 : ℝ)|^8413 ≤ (21427794320983/100000000000000 : ℝ)^6365
        have hw : |(155886853/500000000 : ℝ)|=(155886853/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(704381013/1250000000 : ℝ)|^8413 ≤ (46853985890221/100000000000000 : ℝ)^6365
        have hw : |(704381013/1250000000 : ℝ)|=(704381013/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s0_4 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1872287771/10000000000 : ℝ)*x 0 + (192894559/400000000 : ℝ)*x 1 + (1500809147/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1872287771/10000000000 : ℝ)^8413 ≤ (10920725301001/100000000000000 : ℝ)^6365 := by
    have hnat : (1872287771 : ℕ)^8413*100000000000000^6365 ≤ 10920725301001^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1872287771 10000000000 10920725301001 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (192894559/400000000 : ℝ)^8413 ≤ (19068469796393/50000000000000 : ℝ)^6365 := by
    have hnat : (192894559 : ℕ)^8413*50000000000000^6365 ≤ 19068469796393^6365*400000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192894559 400000000 19068469796393 50000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1500809147/2500000000 : ℝ)^8413 ≤ (3183895942939/6250000000000 : ℝ)^6365 := by
    have hnat : (1500809147 : ℕ)^8413*6250000000000^6365 ≤ 3183895942939^6365*2500000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1500809147 2500000000 3183895942939 6250000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1872287771/10000000000 : ℝ), (192894559/400000000 : ℝ), (1500809147/2500000000 : ℝ)] ![(10920725301001/100000000000000 : ℝ), (19068469796393/50000000000000 : ℝ), (3183895942939/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1872287771/10000000000 : ℝ)|^8413 ≤ (10920725301001/100000000000000 : ℝ)^6365
        have hw : |(-1872287771/10000000000 : ℝ)|=(1872287771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(192894559/400000000 : ℝ)|^8413 ≤ (19068469796393/50000000000000 : ℝ)^6365
        have hw : |(192894559/400000000 : ℝ)|=(192894559/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1500809147/2500000000 : ℝ)|^8413 ≤ (3183895942939/6250000000000 : ℝ)^6365
        have hw : |(1500809147/2500000000 : ℝ)|=(1500809147/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s0_5 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5173414869/10000000000 : ℝ)*x 0 + (-1367417863/10000000000 : ℝ)*x 1 + (6003238447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5173414869/10000000000 : ℝ)^8413 ≤ (41848741404091/100000000000000 : ℝ)^6365 := by
    have hnat : (5173414869 : ℕ)^8413*100000000000000^6365 ≤ 41848741404091^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173414869 10000000000 41848741404091 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1367417863/10000000000 : ℝ)^8413 ≤ (7208902646753/100000000000000 : ℝ)^6365 := by
    have hnat : (1367417863 : ℕ)^8413*100000000000000^6365 ≤ 7208902646753^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367417863 10000000000 7208902646753 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6003238447/10000000000 : ℝ)^8413 ≤ (50942355937947/100000000000000 : ℝ)^6365 := by
    have hnat : (6003238447 : ℕ)^8413*100000000000000^6365 ≤ 50942355937947^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6003238447 10000000000 50942355937947 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5173414869/10000000000 : ℝ), (-1367417863/10000000000 : ℝ), (6003238447/10000000000 : ℝ)] ![(41848741404091/100000000000000 : ℝ), (7208902646753/100000000000000 : ℝ), (50942355937947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5173414869/10000000000 : ℝ)|^8413 ≤ (41848741404091/100000000000000 : ℝ)^6365
        have hw : |(5173414869/10000000000 : ℝ)|=(5173414869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1367417863/10000000000 : ℝ)|^8413 ≤ (7208902646753/100000000000000 : ℝ)^6365
        have hw : |(-1367417863/10000000000 : ℝ)|=(1367417863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6003238447/10000000000 : ℝ)|^8413 ≤ (50942355937947/100000000000000 : ℝ)^6365
        have hw : |(6003238447/10000000000 : ℝ)|=(6003238447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s0_6 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1034683163/2000000000 : ℝ)*x 0 + (1500809259/2500000000 : ℝ)*x 1 + (-683709341/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1034683163/2000000000 : ℝ)^8413 ≤ (41848751518691/100000000000000 : ℝ)^6365 := by
    have hnat : (1034683163 : ℕ)^8413*100000000000000^6365 ≤ 41848751518691^6365*2000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034683163 2000000000 41848751518691 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1500809259/2500000000 : ℝ)^8413 ≤ (50942340111883/100000000000000 : ℝ)^6365 := by
    have hnat : (1500809259 : ℕ)^8413*100000000000000^6365 ≤ 50942340111883^6365*2500000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1500809259 2500000000 50942340111883 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (683709341/5000000000 : ℝ)^8413 ≤ (7208908353707/100000000000000 : ℝ)^6365 := by
    have hnat : (683709341 : ℕ)^8413*100000000000000^6365 ≤ 7208908353707^6365*5000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683709341 5000000000 7208908353707 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1034683163/2000000000 : ℝ), (1500809259/2500000000 : ℝ), (-683709341/5000000000 : ℝ)] ![(41848751518691/100000000000000 : ℝ), (50942340111883/100000000000000 : ℝ), (7208908353707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1034683163/2000000000 : ℝ)|^8413 ≤ (41848751518691/100000000000000 : ℝ)^6365
        have hw : |(1034683163/2000000000 : ℝ)|=(1034683163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1500809259/2500000000 : ℝ)|^8413 ≤ (50942340111883/100000000000000 : ℝ)^6365
        have hw : |(1500809259/2500000000 : ℝ)|=(1500809259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-683709341/5000000000 : ℝ)|^8413 ≤ (7208908353707/100000000000000 : ℝ)^6365
        have hw : |(-683709341/5000000000 : ℝ)|=(683709341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s0_7 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4204693111/10000000000 : ℝ)*x 0 + (2785099057/5000000000 : ℝ)*x 1 + (1592438487/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4204693111/10000000000 : ℝ)^8413 ≤ (3181758365579/10000000000000 : ℝ)^6365 := by
    have hnat : (4204693111 : ℕ)^8413*10000000000000^6365 ≤ 3181758365579^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4204693111 10000000000 3181758365579 10000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2785099057/5000000000 : ℝ)^8413 ≤ (46142601420763/100000000000000 : ℝ)^6365 := by
    have hnat : (2785099057 : ℕ)^8413*100000000000000^6365 ≤ 46142601420763^6365*5000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2785099057 5000000000 46142601420763 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1592438487/5000000000 : ℝ)^8413 ≤ (22039814907867/100000000000000 : ℝ)^6365 := by
    have hnat : (1592438487 : ℕ)^8413*100000000000000^6365 ≤ 22039814907867^6365*5000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1592438487 5000000000 22039814907867 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4204693111/10000000000 : ℝ), (2785099057/5000000000 : ℝ), (1592438487/5000000000 : ℝ)] ![(3181758365579/10000000000000 : ℝ), (46142601420763/100000000000000 : ℝ), (22039814907867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4204693111/10000000000 : ℝ)|^8413 ≤ (3181758365579/10000000000000 : ℝ)^6365
        have hw : |(4204693111/10000000000 : ℝ)|=(4204693111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2785099057/5000000000 : ℝ)|^8413 ≤ (46142601420763/100000000000000 : ℝ)^6365
        have hw : |(2785099057/5000000000 : ℝ)|=(2785099057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1592438487/5000000000 : ℝ)|^8413 ≤ (22039814907867/100000000000000 : ℝ)^6365
        have hw : |(1592438487/5000000000 : ℝ)|=(1592438487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1220_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150997839/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (73/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27519/100000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (2103/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2103 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2103*1^512 ≤ 0^512*1^2103 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2103 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2103 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2103/512 : ℝ) ≤ (2320024138218054783/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2103 ≤ (2320024138218054783/100000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2103*100000000000000000000^512 ≤ 2320024138218054783^512*5^2103 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2320024138218054783 100000000000000000000 2103 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2320024138218054783/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2103 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2103/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2103 := by
      have hnat : (1 : ℕ)^512*1^2103 ≤ 1^2103*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2103 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (102320024138218054783/100000000000000000000 : ℝ) ≤ (5027997318711539/5000000000000000 : ℝ) ^ (2103/512 : ℝ) := by
    have hpowers : (102320024138218054783/100000000000000000000 : ℝ)^512 ≤ (5027997318711539/5000000000000000 : ℝ)^2103 := by
      have hnat : (102320024138218054783 : ℕ)^512*5000000000000000^2103 ≤ 5027997318711539^2103*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102320024138218054783 100000000000000000000 5027997318711539 5000000000000000 512 2103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5027997318711539/5000000000000000 : ℝ)) (X := (102320024138218054783/100000000000000000000 : ℝ)) (by norm_num) 2103 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (52320024138218054783/50000000000000000000 : ℝ) ≤ (2527997318711539/2500000000000000 : ℝ) ^ (2103/512 : ℝ) := by
    have hpowers : (52320024138218054783/50000000000000000000 : ℝ)^512 ≤ (2527997318711539/2500000000000000 : ℝ)^2103 := by
      have hnat : (52320024138218054783 : ℕ)^512*2500000000000000^2103 ≤ 2527997318711539^2103*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52320024138218054783 50000000000000000000 2527997318711539 2500000000000000 512 2103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2527997318711539/2500000000000000 : ℝ)) (X := (52320024138218054783/50000000000000000000 : ℝ)) (by norm_num) 2103 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(27997318711539/2000000000000000 : ℝ)*(0 : ℝ))^(2103/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(27997318711539/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2320024138218054783/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(27997318711539/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2103/512 : ℝ) := by
    rw [show (1 : ℝ)+(27997318711539/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5027997318711539/5000000000000000 : ℝ) by norm_num, show 1+(2320024138218054783/100000000000000000000 : ℝ)+(0 : ℝ)=(102320024138218054783/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2320024138218054783/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(27997318711539/2000000000000000 : ℝ)*(2/5 : ℝ))^(2103/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(27997318711539/2000000000000000 : ℝ)*(2/5 : ℝ)=(2527997318711539/2500000000000000 : ℝ) by norm_num, show 1+2*(2320024138218054783/100000000000000000000 : ℝ)=(52320024138218054783/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(27997318711539/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2103/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27997318711539/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(27997318711539/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2103/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27997318711539/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(27997318711539/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2103/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27997318711539/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1867367353/10000000000 : ℝ)*X 0 0+(6036477493/10000000000 : ℝ)*X 0 1+(4790257199/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((110247979/200000000 : ℝ)*X 1 0+(-645099769/2500000000 : ℝ)*X 1 1+(4790257161/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2756199461/5000000000 : ℝ)*X 2 0+(1197564299/2500000000 : ℝ)*X 2 1+(-2580399069/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((838950979/2000000000 : ℝ)*X 0 0+(155886853/500000000 : ℝ)*X 0 1+(704381013/1250000000 : ℝ)*X 0 2+(838950979/2000000000 : ℝ)*X 1 0+(155886853/500000000 : ℝ)*X 1 1+(704381013/1250000000 : ℝ)*X 1 2+(838950979/2000000000 : ℝ)*X 2 0+(155886853/500000000 : ℝ)*X 2 1+(704381013/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1872287771/10000000000 : ℝ)*X 0 0+(192894559/400000000 : ℝ)*X 0 1+(1500809147/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5173414869/10000000000 : ℝ)*X 1 0+(-1367417863/10000000000 : ℝ)*X 1 1+(6003238447/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1034683163/2000000000 : ℝ)*X 2 0+(1500809259/2500000000 : ℝ)*X 2 1+(-683709341/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4204693111/10000000000 : ℝ)*X 0 0+(2785099057/5000000000 : ℝ)*X 0 1+(1592438487/5000000000 : ℝ)*X 0 2+(4204693111/10000000000 : ℝ)*X 1 0+(2785099057/5000000000 : ℝ)*X 1 1+(1592438487/5000000000 : ℝ)*X 1 2+(4204693111/10000000000 : ℝ)*X 2 0+(2785099057/5000000000 : ℝ)*X 2 1+(1592438487/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16236371025432673424817/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4629959/6250000000000 : ℝ)*(base1) + (317308853/20000000000000 : ℝ)*(base19) + (184241593/12500000000000 : ℝ)*(base23) + (54267797/50000000000000 : ℝ)*(base24) + (361460287/100000000000000 : ℝ)*(upper3) + (59984455470601/10000000000000 : ℝ)*(major0) + (59984455470601/10000000000000 : ℝ)*(major1) + (59984455470601/10000000000000 : ℝ)*(major2) + (40121585787817/5000000000000 : ℝ)*(sp0) + (32097342868313/4000000000000 : ℝ)*(sp1) + (802433575783753/100000000000000 : ℝ)*(sp2) + (397250896481837/100000000000000 : ℝ)*(sp3) + (703315019/20000000000000 : ℝ)*(sp4) + (2764113797/100000000000000 : ℝ)*(sp7) + (198626867337489/50000000000000 : ℝ)*(f.failure) + (80243515825209/10000000000000 : ℝ)*(f.sum) + (4210580794939/10000000000000000000000000000 : ℝ)*base65 + (87787112495061/20000000000000000000000000000 : ℝ)*base68 + (176826082955061/20000000000000000000000000000 : ℝ)*base70 + (35432352675061/20000000000000000000000000000 : ℝ)*base72 + (8596669815061/10000000000000000000000000000 : ℝ)*base74 + (7576429055061/20000000000000000000000000000 : ℝ)*base76 + (57542962995061/20000000000000000000000000000 : ℝ)*base78 + (102904679355061/20000000000000000000000000000 : ℝ)*base80 + (7208499725061/10000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (22686271/5000000000000000000000 : ℝ)*base89 + (22686271/5000000000000000000000 : ℝ)*base91 + (22686271/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (656335955912094483875151/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17150047/100000000000000 : ℝ)*(base1) + (455746143/25000000000000 : ℝ)*(base19) + (2000998929/100000000000000 : ℝ)*(base23) + (11743761/3125000000000 : ℝ)*(upper3) + (7726509/10000000000000 : ℝ)*(upper5) + (633030750883699/100000000000000 : ℝ)*(major0) + (633030750883699/100000000000000 : ℝ)*(major1) + (633030750883699/100000000000000 : ℝ)*(major2) + (2060762049/50000000000000 : ℝ)*(sp1) + (279692081/6250000000000 : ℝ)*(sp2) + (846829637569299/100000000000000 : ℝ)*(sp4) + (846823675910581/100000000000000 : ℝ)*(sp5) + (423411572173513/50000000000000 : ℝ)*(sp6) + (419231645419441/100000000000000 : ℝ)*(sp7) + (26201978910593/6250000000000 : ℝ)*(f.failure) + (211707405104813/25000000000000 : ℝ)*(f.sum) + (9829476102761/100000000000000000000000000000 : ℝ)*base65 + (842775241497239/200000000000000000000000000000 : ℝ)*base68 + (698339649102761/200000000000000000000000000000 : ℝ)*base69 + (698792930302761/200000000000000000000000000000 : ℝ)*base71 + (386236923997239/100000000000000000000000000000 : ℝ)*base74 + (1272427314502761/200000000000000000000000000000 : ℝ)*base75 + (1134137507702761/200000000000000000000000000000 : ℝ)*base77 + (107726873102761/200000000000000000000000000000 : ℝ)*base79 + (22957280502761/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1541473/625000000000000000000 : ℝ)*base90 + (1541473/625000000000000000000 : ℝ)*base92 + (1541473/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1220_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150997839/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (73/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27519/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1220_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1220_s1_0 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1033187863/5000000000 : ℝ)*x 0 + (5681171333/10000000000 : ℝ)*x 1 + (313635943/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1033187863/5000000000 : ℝ)^8413 ≤ (12441458387033/100000000000000 : ℝ)^6365 := by
    have hnat : (1033187863 : ℕ)^8413*100000000000000^6365 ≤ 12441458387033^6365*5000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033187863 5000000000 12441458387033 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5681171333/10000000000 : ℝ)^8413 ≤ (75778481213/160000000000 : ℝ)^6365 := by
    have hnat : (5681171333 : ℕ)^8413*160000000000^6365 ≤ 75778481213^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5681171333 10000000000 75778481213 160000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (313635943/625000000 : ℝ)^8413 ≤ (40196990841293/100000000000000 : ℝ)^6365 := by
    have hnat : (313635943 : ℕ)^8413*100000000000000^6365 ≤ 40196990841293^6365*625000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      313635943 625000000 40196990841293 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1033187863/5000000000 : ℝ), (5681171333/10000000000 : ℝ), (313635943/625000000 : ℝ)] ![(12441458387033/100000000000000 : ℝ), (75778481213/160000000000 : ℝ), (40196990841293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1033187863/5000000000 : ℝ)|^8413 ≤ (12441458387033/100000000000000 : ℝ)^6365
        have hw : |(-1033187863/5000000000 : ℝ)|=(1033187863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5681171333/10000000000 : ℝ)|^8413 ≤ (75778481213/160000000000 : ℝ)^6365
        have hw : |(5681171333/10000000000 : ℝ)|=(5681171333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(313635943/625000000 : ℝ)|^8413 ≤ (40196990841293/100000000000000 : ℝ)^6365
        have hw : |(313635943/625000000 : ℝ)|=(313635943/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s1_1 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2707428239/5000000000 : ℝ)*x 0 + (-15142353/62500000 : ℝ)*x 1 + (5018175061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2707428239/5000000000 : ℝ)^8413 ≤ (8889881730003/20000000000000 : ℝ)^6365 := by
    have hnat : (2707428239 : ℕ)^8413*20000000000000^6365 ≤ 8889881730003^6365*5000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707428239 5000000000 8889881730003 20000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15142353/62500000 : ℝ)^8413 ≤ (7676800394037/50000000000000 : ℝ)^6365 := by
    have hnat : (15142353 : ℕ)^8413*50000000000000^6365 ≤ 7676800394037^6365*62500000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15142353 62500000 7676800394037 50000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5018175061/10000000000 : ℝ)^8413 ≤ (20098495277713/50000000000000 : ℝ)^6365 := by
    have hnat : (5018175061 : ℕ)^8413*50000000000000^6365 ≤ 20098495277713^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5018175061 10000000000 20098495277713 50000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2707428239/5000000000 : ℝ), (-15142353/62500000 : ℝ), (5018175061/10000000000 : ℝ)] ![(8889881730003/20000000000000 : ℝ), (7676800394037/50000000000000 : ℝ), (20098495277713/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2707428239/5000000000 : ℝ)|^8413 ≤ (8889881730003/20000000000000 : ℝ)^6365
        have hw : |(2707428239/5000000000 : ℝ)|=(2707428239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-15142353/62500000 : ℝ)|^8413 ≤ (7676800394037/50000000000000 : ℝ)^6365
        have hw : |(-15142353/62500000 : ℝ)|=(15142353/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5018175061/10000000000 : ℝ)|^8413 ≤ (20098495277713/50000000000000 : ℝ)^6365
        have hw : |(5018175061/10000000000 : ℝ)|=(5018175061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s1_2 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5414856479/10000000000 : ℝ)*x 0 + (5018175087/10000000000 : ℝ)*x 1 + (-484555289/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5414856479/10000000000 : ℝ)^8413 ≤ (8889881732173/20000000000000 : ℝ)^6365 := by
    have hnat : (5414856479 : ℕ)^8413*20000000000000^6365 ≤ 8889881732173^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414856479 10000000000 8889881732173 20000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5018175087/10000000000 : ℝ)^8413 ≤ (8039398166141/20000000000000 : ℝ)^6365 := by
    have hnat : (5018175087 : ℕ)^8413*20000000000000^6365 ≤ 8039398166141^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5018175087 10000000000 8039398166141 20000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (484555289/2000000000 : ℝ)^8413 ≤ (7676800247453/50000000000000 : ℝ)^6365 := by
    have hnat : (484555289 : ℕ)^8413*50000000000000^6365 ≤ 7676800247453^6365*2000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      484555289 2000000000 7676800247453 50000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5414856479/10000000000 : ℝ), (5018175087/10000000000 : ℝ), (-484555289/2000000000 : ℝ)] ![(8889881732173/20000000000000 : ℝ), (8039398166141/20000000000000 : ℝ), (7676800247453/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5414856479/10000000000 : ℝ)|^8413 ≤ (8889881732173/20000000000000 : ℝ)^6365
        have hw : |(5414856479/10000000000 : ℝ)|=(5414856479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5018175087/10000000000 : ℝ)|^8413 ≤ (8039398166141/20000000000000 : ℝ)^6365
        have hw : |(5018175087/10000000000 : ℝ)|=(5018175087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-484555289/2000000000 : ℝ)|^8413 ≤ (7676800247453/50000000000000 : ℝ)^6365
        have hw : |(-484555289/2000000000 : ℝ)|=(484555289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s1_3 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2155379909/5000000000 : ℝ)*x 0 + (922862377/2500000000 : ℝ)*x 1 + (2515336967/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155379909/5000000000 : ℝ)^8413 ≤ (32882740324591/100000000000000 : ℝ)^6365 := by
    have hnat : (2155379909 : ℕ)^8413*100000000000000^6365 ≤ 32882740324591^6365*5000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155379909 5000000000 32882740324591 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (922862377/2500000000 : ℝ)^8413 ≤ (13393941106523/50000000000000 : ℝ)^6365 := by
    have hnat : (922862377 : ℕ)^8413*50000000000000^6365 ≤ 13393941106523^6365*2500000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      922862377 2500000000 13393941106523 50000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2515336967/5000000000 : ℝ)^8413 ≤ (8065875487881/20000000000000 : ℝ)^6365 := by
    have hnat : (2515336967 : ℕ)^8413*20000000000000^6365 ≤ 8065875487881^6365*5000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2515336967 5000000000 8065875487881 20000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2155379909/5000000000 : ℝ), (922862377/2500000000 : ℝ), (2515336967/5000000000 : ℝ)] ![(32882740324591/100000000000000 : ℝ), (13393941106523/50000000000000 : ℝ), (8065875487881/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2155379909/5000000000 : ℝ)|^8413 ≤ (32882740324591/100000000000000 : ℝ)^6365
        have hw : |(2155379909/5000000000 : ℝ)|=(2155379909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(922862377/2500000000 : ℝ)|^8413 ≤ (13393941106523/50000000000000 : ℝ)^6365
        have hw : |(922862377/2500000000 : ℝ)|=(922862377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2515336967/5000000000 : ℝ)|^8413 ≤ (8065875487881/20000000000000 : ℝ)^6365
        have hw : |(2515336967/5000000000 : ℝ)|=(2515336967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s1_4 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-206707513/1000000000 : ℝ)*x 0 + (5026957099/10000000000 : ℝ)*x 1 + (2836111629/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (206707513/1000000000 : ℝ)^8413 ≤ (12447024682283/100000000000000 : ℝ)^6365 := by
    have hnat : (206707513 : ℕ)^8413*100000000000000^6365 ≤ 12447024682283^6365*1000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206707513 1000000000 12447024682283 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5026957099/10000000000 : ℝ)^8413 ≤ (40289998004637/100000000000000 : ℝ)^6365 := by
    have hnat : (5026957099 : ℕ)^8413*100000000000000^6365 ≤ 40289998004637^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5026957099 10000000000 40289998004637 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2836111629/5000000000 : ℝ)^8413 ≤ (11815744323243/25000000000000 : ℝ)^6365 := by
    have hnat : (2836111629 : ℕ)^8413*25000000000000^6365 ≤ 11815744323243^6365*5000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2836111629 5000000000 11815744323243 25000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-206707513/1000000000 : ℝ), (5026957099/10000000000 : ℝ), (2836111629/5000000000 : ℝ)] ![(12447024682283/100000000000000 : ℝ), (40289998004637/100000000000000 : ℝ), (11815744323243/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-206707513/1000000000 : ℝ)|^8413 ≤ (12447024682283/100000000000000 : ℝ)^6365
        have hw : |(-206707513/1000000000 : ℝ)|=(206707513/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5026957099/10000000000 : ℝ)|^8413 ≤ (40289998004637/100000000000000 : ℝ)^6365
        have hw : |(5026957099/10000000000 : ℝ)|=(5026957099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2836111629/5000000000 : ℝ)|^8413 ≤ (11815744323243/25000000000000 : ℝ)^6365
        have hw : |(2836111629/5000000000 : ℝ)|=(2836111629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s1_5 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2622113733/5000000000 : ℝ)*x 0 + (-22109167/125000000 : ℝ)*x 1 + (5672217383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2622113733/5000000000 : ℝ)^8413 ≤ (2130376471121/5000000000000 : ℝ)^6365 := by
    have hnat : (2622113733 : ℕ)^8413*5000000000000^6365 ≤ 2130376471121^6365*5000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622113733 5000000000 2130376471121 5000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (22109167/125000000 : ℝ)^8413 ≤ (2532389491537/25000000000000 : ℝ)^6365 := by
    have hnat : (22109167 : ℕ)^8413*25000000000000^6365 ≤ 2532389491537^6365*125000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22109167 125000000 2532389491537 25000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5672217383/10000000000 : ℝ)^8413 ≤ (47262912589433/100000000000000 : ℝ)^6365 := by
    have hnat : (5672217383 : ℕ)^8413*100000000000000^6365 ≤ 47262912589433^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5672217383 10000000000 47262912589433 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2622113733/5000000000 : ℝ), (-22109167/125000000 : ℝ), (5672217383/10000000000 : ℝ)] ![(2130376471121/5000000000000 : ℝ), (2532389491537/25000000000000 : ℝ), (47262912589433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2622113733/5000000000 : ℝ)|^8413 ≤ (2130376471121/5000000000000 : ℝ)^6365
        have hw : |(2622113733/5000000000 : ℝ)|=(2622113733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-22109167/125000000 : ℝ)|^8413 ≤ (2532389491537/25000000000000 : ℝ)^6365
        have hw : |(-22109167/125000000 : ℝ)|=(22109167/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5672217383/10000000000 : ℝ)|^8413 ≤ (47262912589433/100000000000000 : ℝ)^6365
        have hw : |(5672217383/10000000000 : ℝ)|=(5672217383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s1_6 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5244227591/10000000000 : ℝ)*x 0 + (709027231/1250000000 : ℝ)*x 1 + (-1768732507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5244227591/10000000000 : ℝ)^8413 ≤ (1704301230591/4000000000000 : ℝ)^6365 := by
    have hnat : (5244227591 : ℕ)^8413*4000000000000^6365 ≤ 1704301230591^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244227591 10000000000 1704301230591 4000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (709027231/1250000000 : ℝ)^8413 ≤ (5907864713831/12500000000000 : ℝ)^6365 := by
    have hnat : (709027231 : ℕ)^8413*12500000000000^6365 ≤ 5907864713831^6365*1250000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      709027231 1250000000 5907864713831 12500000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1768732507/10000000000 : ℝ)^8413 ≤ (5064775754583/50000000000000 : ℝ)^6365 := by
    have hnat : (1768732507 : ℕ)^8413*50000000000000^6365 ≤ 5064775754583^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1768732507 10000000000 5064775754583 50000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5244227591/10000000000 : ℝ), (709027231/1250000000 : ℝ), (-1768732507/10000000000 : ℝ)] ![(1704301230591/4000000000000 : ℝ), (5907864713831/12500000000000 : ℝ), (5064775754583/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5244227591/10000000000 : ℝ)|^8413 ≤ (1704301230591/4000000000000 : ℝ)^6365
        have hw : |(5244227591/10000000000 : ℝ)|=(5244227591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(709027231/1250000000 : ℝ)|^8413 ≤ (5907864713831/12500000000000 : ℝ)^6365
        have hw : |(709027231/1250000000 : ℝ)|=(709027231/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1768732507/10000000000 : ℝ)|^8413 ≤ (5064775754583/50000000000000 : ℝ)^6365
        have hw : |(-1768732507/10000000000 : ℝ)|=(1768732507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s1_7 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4312178513/10000000000 : ℝ)*x 0 + (5012929171/10000000000 : ℝ)*x 1 + (3709535839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4312178513/10000000000 : ℝ)^8413 ≤ (3289704502241/10000000000000 : ℝ)^6365 := by
    have hnat : (4312178513 : ℕ)^8413*10000000000000^6365 ≤ 3289704502241^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4312178513 10000000000 3289704502241 10000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5012929171/10000000000 : ℝ)^8413 ≤ (40141458169967/100000000000000 : ℝ)^6365 := by
    have hnat : (5012929171 : ℕ)^8413*100000000000000^6365 ≤ 40141458169967^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5012929171 10000000000 40141458169967 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3709535839/10000000000 : ℝ)^8413 ≤ (13480748400997/50000000000000 : ℝ)^6365 := by
    have hnat : (3709535839 : ℕ)^8413*50000000000000^6365 ≤ 13480748400997^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3709535839 10000000000 13480748400997 50000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4312178513/10000000000 : ℝ), (5012929171/10000000000 : ℝ), (3709535839/10000000000 : ℝ)] ![(3289704502241/10000000000000 : ℝ), (40141458169967/100000000000000 : ℝ), (13480748400997/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4312178513/10000000000 : ℝ)|^8413 ≤ (3289704502241/10000000000000 : ℝ)^6365
        have hw : |(4312178513/10000000000 : ℝ)|=(4312178513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5012929171/10000000000 : ℝ)|^8413 ≤ (40141458169967/100000000000000 : ℝ)^6365
        have hw : |(5012929171/10000000000 : ℝ)|=(5012929171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3709535839/10000000000 : ℝ)|^8413 ≤ (13480748400997/50000000000000 : ℝ)^6365
        have hw : |(3709535839/10000000000 : ℝ)|=(3709535839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1220_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150997839/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27519/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (73/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (243/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20093/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27519/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (73/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27519/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (73/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27519/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (73/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27519/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (73/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27519/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (73/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27519/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (73/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (73/10000 : ℝ) ^ (2103/512 : ℝ) ≤ (20925487709/12500000000000000000 : ℝ) := by
    have hpowers : (73/10000 : ℝ)^2103 ≤ (20925487709/12500000000000000000 : ℝ)^512 := by
      have hnat : (73 : ℕ)^2103*12500000000000000000^512 ≤ 20925487709^512*10000^2103 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        73 10000 20925487709 12500000000000000000 2103 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (73/10000 : ℝ)) (X := (20925487709/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2103 512 (by norm_num) hpowers
    exact h
  have hpowhi : (27519/100000 : ℝ) ^ (2103/512 : ℝ) ≤ (499269321985330243/100000000000000000000 : ℝ) := by
    have hpowers : (27519/100000 : ℝ)^2103 ≤ (499269321985330243/100000000000000000000 : ℝ)^512 := by
      have hnat : (27519 : ℕ)^2103*100000000000000000000^512 ≤ 499269321985330243^512*100000^2103 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27519 100000 499269321985330243 100000000000000000000 2103 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27519/100000 : ℝ)) (X := (499269321985330243/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2103 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250000020925487709/6250000000000000000 : ℝ) ≤ (10000000008151289/10000000000000000 : ℝ) ^ (2103/512 : ℝ) := by
    have hpowers : (6250000020925487709/6250000000000000000 : ℝ)^512 ≤ (10000000008151289/10000000000000000 : ℝ)^2103 := by
      have hnat : (6250000020925487709 : ℕ)^512*10000000000000000^2103 ≤ 10000000008151289^2103*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250000020925487709 6250000000000000000 10000000008151289 10000000000000000 512 2103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000008151289/10000000000000000 : ℝ)) (X := (6250000020925487709/6250000000000000000 : ℝ)) (by norm_num) 2103 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20099853897877846383/20000000000000000000 : ℝ) ≤ (10012132411520813/10000000000000000 : ℝ) ^ (2103/512 : ℝ) := by
    have hpowers : (20099853897877846383/20000000000000000000 : ℝ)^512 ≤ (10012132411520813/10000000000000000 : ℝ)^2103 := by
      have hnat : (20099853897877846383 : ℕ)^512*10000000000000000^2103 ≤ 10012132411520813^2103*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20099853897877846383 20000000000000000000 10012132411520813 10000000000000000 512 2103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10012132411520813/10000000000000000 : ℝ)) (X := (20099853897877846383/20000000000000000000 : ℝ)) (by norm_num) 2103 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50499269321985330243/50000000000000000000 : ℝ) ≤ (10024264814890337/10000000000000000 : ℝ) ^ (2103/512 : ℝ) := by
    have hpowers : (50499269321985330243/50000000000000000000 : ℝ)^512 ≤ (10024264814890337/10000000000000000 : ℝ)^2103 := by
      have hnat : (50499269321985330243 : ℕ)^512*10000000000000000^2103 ≤ 10024264814890337^2103*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50499269321985330243 50000000000000000000 10024264814890337 10000000000000000 512 2103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10024264814890337/10000000000000000 : ℝ)) (X := (50499269321985330243/50000000000000000000 : ℝ)) (by norm_num) 2103 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(20925487709/12500000000000000000 : ℝ) ≤ ((267872286909445375981/267890000000000000000 : ℝ)+2*(3033100842381/669725000000000 : ℝ)*(73/10000 : ℝ))^(2103/512 : ℝ) := by
    rw [show (267872286909445375981/267890000000000000000 : ℝ)+2*(3033100842381/669725000000000 : ℝ)*(73/10000 : ℝ)=(10000000008151289/10000000000000000 : ℝ) by norm_num, show 1+2*(20925487709/12500000000000000000 : ℝ)=(6250000020925487709/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(499269321985330243/100000000000000000000 : ℝ)+(20925487709/12500000000000000000 : ℝ) ≤ ((267872286909445375981/267890000000000000000 : ℝ)+(3033100842381/669725000000000 : ℝ)*((27519/100000 : ℝ)+(73/10000 : ℝ)))^(2103/512 : ℝ) := by
    rw [show (267872286909445375981/267890000000000000000 : ℝ)+(3033100842381/669725000000000 : ℝ)*((27519/100000 : ℝ)+(73/10000 : ℝ))=(10012132411520813/10000000000000000 : ℝ) by norm_num, show 1+(499269321985330243/100000000000000000000 : ℝ)+(20925487709/12500000000000000000 : ℝ)=(20099853897877846383/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(499269321985330243/100000000000000000000 : ℝ) ≤ ((267872286909445375981/267890000000000000000 : ℝ)+2*(3033100842381/669725000000000 : ℝ)*(27519/100000 : ℝ))^(2103/512 : ℝ) := by
    rw [show (267872286909445375981/267890000000000000000 : ℝ)+2*(3033100842381/669725000000000 : ℝ)*(27519/100000 : ℝ)=(10024264814890337/10000000000000000 : ℝ) by norm_num, show 1+2*(499269321985330243/100000000000000000000 : ℝ)=(50499269321985330243/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (267872286909445375981/267890000000000000000 : ℝ)*(X 1 0+X 2 0)+(3033100842381/669725000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2103/512 : ℝ)) (lo := (73/10000 : ℝ)) (hi := (27519/100000 : ℝ)) (c := (267872286909445375981/267890000000000000000 : ℝ)) (alpha := (3033100842381/669725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (267872286909445375981/267890000000000000000 : ℝ)*(X 0 1+X 2 1)+(3033100842381/669725000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2103/512 : ℝ)) (lo := (73/10000 : ℝ)) (hi := (27519/100000 : ℝ)) (c := (267872286909445375981/267890000000000000000 : ℝ)) (alpha := (3033100842381/669725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (267872286909445375981/267890000000000000000 : ℝ)*(X 0 2+X 1 2)+(3033100842381/669725000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2103/512 : ℝ)) (lo := (73/10000 : ℝ)) (hi := (27519/100000 : ℝ)) (c := (267872286909445375981/267890000000000000000 : ℝ)) (alpha := (3033100842381/669725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1033187863/5000000000 : ℝ)*X 0 0+(5681171333/10000000000 : ℝ)*X 0 1+(313635943/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2707428239/5000000000 : ℝ)*X 1 0+(-15142353/62500000 : ℝ)*X 1 1+(5018175061/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5414856479/10000000000 : ℝ)*X 2 0+(5018175087/10000000000 : ℝ)*X 2 1+(-484555289/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2155379909/5000000000 : ℝ)*X 0 0+(922862377/2500000000 : ℝ)*X 0 1+(2515336967/5000000000 : ℝ)*X 0 2+(2155379909/5000000000 : ℝ)*X 1 0+(922862377/2500000000 : ℝ)*X 1 1+(2515336967/5000000000 : ℝ)*X 1 2+(2155379909/5000000000 : ℝ)*X 2 0+(922862377/2500000000 : ℝ)*X 2 1+(2515336967/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-206707513/1000000000 : ℝ)*X 0 0+(5026957099/10000000000 : ℝ)*X 0 1+(2836111629/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2622113733/5000000000 : ℝ)*X 1 0+(-22109167/125000000 : ℝ)*X 1 1+(5672217383/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5244227591/10000000000 : ℝ)*X 2 0+(709027231/1250000000 : ℝ)*X 2 1+(-1768732507/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4312178513/10000000000 : ℝ)*X 0 0+(5012929171/10000000000 : ℝ)*X 0 1+(3709535839/10000000000 : ℝ)*X 0 2+(4312178513/10000000000 : ℝ)*X 1 0+(5012929171/10000000000 : ℝ)*X 1 1+(3709535839/10000000000 : ℝ)*X 1 2+(4312178513/10000000000 : ℝ)*X 2 0+(5012929171/10000000000 : ℝ)*X 2 1+(3709535839/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5557707646955941476452460549/1339450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3469687/6250000000000 : ℝ)*(base1) + (926268329/100000000000000 : ℝ)*(base19) + (2895459/312500000000 : ℝ)*(base23) + (101618579/100000000000000 : ℝ)*(upper3) + (7162319/6250000000000 : ℝ)*(upper5) + (112751004486957/10000000000000 : ℝ)*(major0) + (112751004486957/10000000000000 : ℝ)*(major1) + (112751004486957/10000000000000 : ℝ)*(major2) + (1508308913277761/100000000000000 : ℝ)*(sp0) + (60332517796227/4000000000000 : ℝ)*(sp1) + (377078236156781/25000000000000 : ℝ)*(sp2) + (93337928080909/12500000000000 : ℝ)*(sp3) + (1002682247/20000000000000 : ℝ)*(sp4) + (520018933/20000000000000 : ℝ)*(sp7) + (74670608025693/10000000000000 : ℝ)*(f.failure) + (377078467793501/25000000000000 : ℝ)*(f.sum) + (19278341263591/26789000000000000000000000000 : ℝ)*base65 + (7754412224128279817/2678900000000000000000000000000000 : ℝ)*base67 + (7405402421081479817/2678900000000000000000000000000000 : ℝ)*base69 + (12106245835362479817/2678900000000000000000000000000000 : ℝ)*base71 + (67696333982063/26789000000000000000000000000 : ℝ)*base74 + (2030351970743820183/2678900000000000000000000000000000 : ℝ)*base76 + (14094461802203079817/2678900000000000000000000000000000 : ℝ)*base77 + (11833777200850720183/2678900000000000000000000000000000 : ℝ)*base80 + (15193159882631/26789000000000000000000000000 : ℝ)*base82 + (522573/1000000000000000000000 : ℝ)*base90 + (522573/1000000000000000000000 : ℝ)*base92 + (522573/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7185344260125467673174871107/837156250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (124825329/25000000000000 : ℝ)*(base19) + (1730784579/100000000000000 : ℝ)*(base23) + (148663791/100000000000000 : ℝ)*(lower3) + (521616683/100000000000000 : ℝ)*(lower4) + (72405971290967/6250000000000 : ℝ)*(major0) + (72405971290967/6250000000000 : ℝ)*(major1) + (72405971290967/6250000000000 : ℝ)*(major2) + (2093317107/25000000000000 : ℝ)*(sp0) + (7324271/25000000000000 : ℝ)*(sp1) + (3086494183/50000000000000 : ℝ)*(sp2) + (154975585212557/10000000000000 : ℝ)*(sp4) + (774881848397799/50000000000000 : ℝ)*(sp5) + (1549756321621053/100000000000000 : ℝ)*(sp6) + (767226569815659/100000000000000 : ℝ)*(sp7) + (767226569815659/100000000000000 : ℝ)*(f.failure) + (774882112696999/50000000000000 : ℝ)*(f.sum) + (391971959132473/133945000000000000000000000000 : ℝ)*base65 + (6839476066651926127/1674312500000000000000000000000000 : ℝ)*base67 + (4989784385352051127/1674312500000000000000000000000000 : ℝ)*base69 + (9252235314682176127/1674312500000000000000000000000000 : ℝ)*base71 + (266482525239223/133945000000000000000000000000 : ℝ)*base73 + (2904807508887926127/1674312500000000000000000000000000 : ℝ)*base75 + (12412681290581363627/1674312500000000000000000000000000 : ℝ)*base77 + (5662943651436426127/1674312500000000000000000000000000 : ℝ)*base79 + (7101203617133/8371562500000000000000000000 : ℝ)*base81 + (62639099/10000000000000000000000 : ℝ)*base90 + (62639099/10000000000000000000000 : ℝ)*base92 + (62639099/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1220_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150997839/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27519/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (73/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (243/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20093/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1220_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1220_s2_0 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2115528499/10000000000 : ℝ)*x 0 + (549658997/1000000000 : ℝ)*x 1 + (5171429807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2115528499/10000000000 : ℝ)^8413 ≤ (12834114616789/100000000000000 : ℝ)^6365 := by
    have hnat : (2115528499 : ℕ)^8413*100000000000000^6365 ≤ 12834114616789^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115528499 10000000000 12834114616789 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (549658997/1000000000 : ℝ)^8413 ≤ (45338366877357/100000000000000 : ℝ)^6365 := by
    have hnat : (549658997 : ℕ)^8413*100000000000000^6365 ≤ 45338366877357^6365*1000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549658997 1000000000 45338366877357 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5171429807/10000000000 : ℝ)^8413 ≤ (2614219906167/6250000000000 : ℝ)^6365 := by
    have hnat : (5171429807 : ℕ)^8413*6250000000000^6365 ≤ 2614219906167^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171429807 10000000000 2614219906167 6250000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2115528499/10000000000 : ℝ), (549658997/1000000000 : ℝ), (5171429807/10000000000 : ℝ)] ![(12834114616789/100000000000000 : ℝ), (45338366877357/100000000000000 : ℝ), (2614219906167/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2115528499/10000000000 : ℝ)|^8413 ≤ (12834114616789/100000000000000 : ℝ)^6365
        have hw : |(-2115528499/10000000000 : ℝ)|=(2115528499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(549658997/1000000000 : ℝ)|^8413 ≤ (45338366877357/100000000000000 : ℝ)^6365
        have hw : |(549658997/1000000000 : ℝ)|=(549658997/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5171429807/10000000000 : ℝ)|^8413 ≤ (2614219906167/6250000000000 : ℝ)^6365
        have hw : |(5171429807/10000000000 : ℝ)|=(5171429807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s2_1 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5370586859/10000000000 : ℝ)*x 0 + (-285511237/1250000000 : ℝ)*x 1 + (258571487/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370586859/10000000000 : ℝ)^8413 ≤ (8793942850953/20000000000000 : ℝ)^6365 := by
    have hnat : (5370586859 : ℕ)^8413*20000000000000^6365 ≤ 8793942850953^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370586859 10000000000 8793942850953 20000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (285511237/1250000000 : ℝ)^8413 ≤ (14202767945677/100000000000000 : ℝ)^6365 := by
    have hnat : (285511237 : ℕ)^8413*100000000000000^6365 ≤ 14202767945677^6365*1250000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285511237 1250000000 14202767945677 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258571487/500000000 : ℝ)^8413 ≤ (41827517782399/100000000000000 : ℝ)^6365 := by
    have hnat : (258571487 : ℕ)^8413*100000000000000^6365 ≤ 41827517782399^6365*500000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258571487 500000000 41827517782399 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370586859/10000000000 : ℝ), (-285511237/1250000000 : ℝ), (258571487/500000000 : ℝ)] ![(8793942850953/20000000000000 : ℝ), (14202767945677/100000000000000 : ℝ), (41827517782399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370586859/10000000000 : ℝ)|^8413 ≤ (8793942850953/20000000000000 : ℝ)^6365
        have hw : |(5370586859/10000000000 : ℝ)|=(5370586859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-285511237/1250000000 : ℝ)|^8413 ≤ (14202767945677/100000000000000 : ℝ)^6365
        have hw : |(-285511237/1250000000 : ℝ)|=(285511237/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(258571487/500000000 : ℝ)|^8413 ≤ (41827517782399/100000000000000 : ℝ)^6365
        have hw : |(258571487/500000000 : ℝ)|=(258571487/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s2_2 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2685293331/5000000000 : ℝ)*x 0 + (1034285983/2000000000 : ℝ)*x 1 + (-285511241/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685293331/5000000000 : ℝ)^8413 ≤ (8793942424589/20000000000000 : ℝ)^6365 := by
    have hnat : (2685293331 : ℕ)^8413*20000000000000^6365 ≤ 8793942424589^6365*5000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685293331 5000000000 8793942424589 20000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1034285983/2000000000 : ℝ)^8413 ≤ (20913759826631/50000000000000 : ℝ)^6365 := by
    have hnat : (1034285983 : ℕ)^8413*50000000000000^6365 ≤ 20913759826631^6365*2000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034285983 2000000000 20913759826631 50000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (285511241/1250000000 : ℝ)^8413 ≤ (14202768208681/100000000000000 : ℝ)^6365 := by
    have hnat : (285511241 : ℕ)^8413*100000000000000^6365 ≤ 14202768208681^6365*1250000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285511241 1250000000 14202768208681 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685293331/5000000000 : ℝ), (1034285983/2000000000 : ℝ), (-285511241/1250000000 : ℝ)] ![(8793942424589/20000000000000 : ℝ), (20913759826631/50000000000000 : ℝ), (14202768208681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685293331/5000000000 : ℝ)|^8413 ≤ (8793942424589/20000000000000 : ℝ)^6365
        have hw : |(2685293331/5000000000 : ℝ)|=(2685293331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1034285983/2000000000 : ℝ)|^8413 ≤ (20913759826631/50000000000000 : ℝ)^6365
        have hw : |(1034285983/2000000000 : ℝ)|=(1034285983/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-285511241/1250000000 : ℝ)|^8413 ≤ (14202768208681/100000000000000 : ℝ)^6365
        have hw : |(-285511241/1250000000 : ℝ)|=(285511241/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s2_3 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (173786551/400000000 : ℝ)*x 0 + (2014170331/5000000000 : ℝ)*x 1 + (2342575209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (173786551/400000000 : ℝ)^8413 ≤ (33225007495371/100000000000000 : ℝ)^6365 := by
    have hnat : (173786551 : ℕ)^8413*100000000000000^6365 ≤ 33225007495371^6365*400000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173786551 400000000 33225007495371 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2014170331/5000000000 : ℝ)^8413 ≤ (15032864616307/50000000000000 : ℝ)^6365 := by
    have hnat : (2014170331 : ℕ)^8413*50000000000000^6365 ≤ 15032864616307^6365*5000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014170331 5000000000 15032864616307 50000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2342575209/5000000000 : ℝ)^8413 ≤ (36709263263667/100000000000000 : ℝ)^6365 := by
    have hnat : (2342575209 : ℕ)^8413*100000000000000^6365 ≤ 36709263263667^6365*5000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2342575209 5000000000 36709263263667 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(173786551/400000000 : ℝ), (2014170331/5000000000 : ℝ), (2342575209/5000000000 : ℝ)] ![(33225007495371/100000000000000 : ℝ), (15032864616307/50000000000000 : ℝ), (36709263263667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(173786551/400000000 : ℝ)|^8413 ≤ (33225007495371/100000000000000 : ℝ)^6365
        have hw : |(173786551/400000000 : ℝ)|=(173786551/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2014170331/5000000000 : ℝ)|^8413 ≤ (15032864616307/50000000000000 : ℝ)^6365
        have hw : |(2014170331/5000000000 : ℝ)|=(2014170331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2342575209/5000000000 : ℝ)|^8413 ≤ (36709263263667/100000000000000 : ℝ)^6365
        have hw : |(2342575209/5000000000 : ℝ)|=(2342575209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s2_4 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-528902909/2500000000 : ℝ)*x 0 + (5173552339/10000000000 : ℝ)*x 1 + (2747223629/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528902909/2500000000 : ℝ)^8413 ≤ (200543457263/1562500000000 : ℝ)^6365 := by
    have hnat : (528902909 : ℕ)^8413*1562500000000^6365 ≤ 200543457263^6365*2500000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528902909 2500000000 200543457263 1562500000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5173552339/10000000000 : ℝ)^8413 ≤ (41850211234961/100000000000000 : ℝ)^6365 := by
    have hnat : (5173552339 : ℕ)^8413*100000000000000^6365 ≤ 41850211234961^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173552339 10000000000 41850211234961 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2747223629/5000000000 : ℝ)^8413 ≤ (1132875187081/2500000000000 : ℝ)^6365 := by
    have hnat : (2747223629 : ℕ)^8413*2500000000000^6365 ≤ 1132875187081^6365*5000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2747223629 5000000000 1132875187081 2500000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-528902909/2500000000 : ℝ), (5173552339/10000000000 : ℝ), (2747223629/5000000000 : ℝ)] ![(200543457263/1562500000000 : ℝ), (41850211234961/100000000000000 : ℝ), (1132875187081/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-528902909/2500000000 : ℝ)|^8413 ≤ (200543457263/1562500000000 : ℝ)^6365
        have hw : |(-528902909/2500000000 : ℝ)|=(528902909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5173552339/10000000000 : ℝ)|^8413 ≤ (41850211234961/100000000000000 : ℝ)^6365
        have hw : |(5173552339/10000000000 : ℝ)|=(5173552339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2747223629/5000000000 : ℝ)|^8413 ≤ (1132875187081/2500000000000 : ℝ)^6365
        have hw : |(2747223629/5000000000 : ℝ)|=(2747223629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s2_5 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (330479001/625000000 : ℝ)*x 0 + (-98053611/500000000 : ℝ)*x 1 + (5494447293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330479001/625000000 : ℝ)^8413 ≤ (21537303963379/50000000000000 : ℝ)^6365 := by
    have hnat : (330479001 : ℕ)^8413*50000000000000^6365 ≤ 21537303963379^6365*625000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330479001 625000000 21537303963379 50000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (98053611/500000000 : ℝ)^8413 ≤ (2902596049481/25000000000000 : ℝ)^6365 := by
    have hnat : (98053611 : ℕ)^8413*25000000000000^6365 ≤ 2902596049481^6365*500000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98053611 500000000 2902596049481 25000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5494447293/10000000000 : ℝ)^8413 ≤ (22657503932389/50000000000000 : ℝ)^6365 := by
    have hnat : (5494447293 : ℕ)^8413*50000000000000^6365 ≤ 22657503932389^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5494447293 10000000000 22657503932389 50000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330479001/625000000 : ℝ), (-98053611/500000000 : ℝ), (5494447293/10000000000 : ℝ)] ![(21537303963379/50000000000000 : ℝ), (2902596049481/25000000000000 : ℝ), (22657503932389/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330479001/625000000 : ℝ)|^8413 ≤ (21537303963379/50000000000000 : ℝ)^6365
        have hw : |(330479001/625000000 : ℝ)|=(330479001/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-98053611/500000000 : ℝ)|^8413 ≤ (2902596049481/25000000000000 : ℝ)^6365
        have hw : |(-98053611/500000000 : ℝ)|=(98053611/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5494447293/10000000000 : ℝ)|^8413 ≤ (22657503932389/50000000000000 : ℝ)^6365
        have hw : |(5494447293/10000000000 : ℝ)|=(5494447293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s2_6 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2643832099/5000000000 : ℝ)*x 0 + (2747223669/5000000000 : ℝ)*x 1 + (-1961071907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643832099/5000000000 : ℝ)^8413 ≤ (43074609886421/100000000000000 : ℝ)^6365 := by
    have hnat : (2643832099 : ℕ)^8413*100000000000000^6365 ≤ 43074609886421^6365*5000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643832099 5000000000 43074609886421 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2747223669/5000000000 : ℝ)^8413 ≤ (44252937847/97656250000 : ℝ)^6365 := by
    have hnat : (2747223669 : ℕ)^8413*97656250000^6365 ≤ 44252937847^6365*5000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2747223669 5000000000 44252937847 97656250000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1961071907/10000000000 : ℝ)^8413 ≤ (580519087429/5000000000000 : ℝ)^6365 := by
    have hnat : (1961071907 : ℕ)^8413*5000000000000^6365 ≤ 580519087429^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1961071907 10000000000 580519087429 5000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643832099/5000000000 : ℝ), (2747223669/5000000000 : ℝ), (-1961071907/10000000000 : ℝ)] ![(43074609886421/100000000000000 : ℝ), (44252937847/97656250000 : ℝ), (580519087429/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643832099/5000000000 : ℝ)|^8413 ≤ (43074609886421/100000000000000 : ℝ)^6365
        have hw : |(2643832099/5000000000 : ℝ)|=(2643832099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2747223669/5000000000 : ℝ)|^8413 ≤ (44252937847/97656250000 : ℝ)^6365
        have hw : |(2747223669/5000000000 : ℝ)|=(2747223669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1961071907/10000000000 : ℝ)|^8413 ≤ (580519087429/5000000000000 : ℝ)^6365
        have hw : |(-1961071907/10000000000 : ℝ)|=(1961071907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s2_7 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4344831187/10000000000 : ℝ)*x 0 + (936172623/2000000000 : ℝ)*x 1 + (4032668527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4344831187/10000000000 : ℝ)^8413 ≤ (8306674922851/25000000000000 : ℝ)^6365 := by
    have hnat : (4344831187 : ℕ)^8413*25000000000000^6365 ≤ 8306674922851^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4344831187 10000000000 8306674922851 25000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (936172623/2000000000 : ℝ)^8413 ≤ (1833243460337/5000000000000 : ℝ)^6365 := by
    have hnat : (936172623 : ℕ)^8413*5000000000000^6365 ≤ 1833243460337^6365*2000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      936172623 2000000000 1833243460337 5000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4032668527/10000000000 : ℝ)^8413 ≤ (7527107772791/25000000000000 : ℝ)^6365 := by
    have hnat : (4032668527 : ℕ)^8413*25000000000000^6365 ≤ 7527107772791^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4032668527 10000000000 7527107772791 25000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4344831187/10000000000 : ℝ), (936172623/2000000000 : ℝ), (4032668527/10000000000 : ℝ)] ![(8306674922851/25000000000000 : ℝ), (1833243460337/5000000000000 : ℝ), (7527107772791/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4344831187/10000000000 : ℝ)|^8413 ≤ (8306674922851/25000000000000 : ℝ)^6365
        have hw : |(4344831187/10000000000 : ℝ)|=(4344831187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(936172623/2000000000 : ℝ)|^8413 ≤ (1833243460337/5000000000000 : ℝ)^6365
        have hw : |(936172623/2000000000 : ℝ)|=(936172623/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4032668527/10000000000 : ℝ)|^8413 ≤ (7527107772791/25000000000000 : ℝ)^6365
        have hw : |(4032668527/10000000000 : ℝ)|=(4032668527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1220_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150997839/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (243/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (9409/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8141/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20093/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (243/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20093/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (243/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20093/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (243/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20093/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (243/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20093/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (243/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20093/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (243/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (243/4000 : ℝ) ^ (2103/512 : ℝ) ≤ (63007378004537/6250000000000000000 : ℝ) := by
    have hpowers : (243/4000 : ℝ)^2103 ≤ (63007378004537/6250000000000000000 : ℝ)^512 := by
      have hnat : (243 : ℕ)^2103*6250000000000000000^512 ≤ 63007378004537^512*4000^2103 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        243 4000 63007378004537 6250000000000000000 2103 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (243/4000 : ℝ)) (X := (63007378004537/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 2103 512 (by norm_num) hpowers
    exact h
  have hpowhi : (20093/100000 : ℝ) ^ (2103/512 : ℝ) ≤ (68593174929559401/50000000000000000000 : ℝ) := by
    have hpowers : (20093/100000 : ℝ)^2103 ≤ (68593174929559401/50000000000000000000 : ℝ)^512 := by
      have hnat : (20093 : ℕ)^2103*50000000000000000000^512 ≤ 68593174929559401^512*100000^2103 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20093 100000 68593174929559401 50000000000000000000 2103 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20093/100000 : ℝ)) (X := (68593174929559401/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2103 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125063007378004537/3125000000000000000 : ℝ) ≤ (2000009817451337/2000000000000000 : ℝ) ^ (2103/512 : ℝ) := by
    have hpowers : (3125063007378004537/3125000000000000000 : ℝ)^512 ≤ (2000009817451337/2000000000000000 : ℝ)^2103 := by
      have hnat : (3125063007378004537 : ℕ)^512*2000000000000000^2103 ≤ 2000009817451337^2103*3125000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125063007378004537 3125000000000000000 2000009817451337 2000000000000000 512 2103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000009817451337/2000000000000000 : ℝ)) (X := (3125063007378004537/3125000000000000000 : ℝ)) (by norm_num) 2103 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50069097233953595697/50000000000000000000 : ℝ) ≤ (5001681374469941/5000000000000000 : ℝ) ^ (2103/512 : ℝ) := by
    have hpowers : (50069097233953595697/50000000000000000000 : ℝ)^512 ≤ (5001681374469941/5000000000000000 : ℝ)^2103 := by
      have hnat : (50069097233953595697 : ℕ)^512*5000000000000000^2103 ≤ 5001681374469941^2103*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50069097233953595697 50000000000000000000 5001681374469941 5000000000000000 512 2103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001681374469941/5000000000000000 : ℝ)) (X := (50069097233953595697/50000000000000000000 : ℝ)) (by norm_num) 2103 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25068593174929559401/25000000000000000000 : ℝ) ≤ (10006676410623079/10000000000000000 : ℝ) ^ (2103/512 : ℝ) := by
    have hpowers : (25068593174929559401/25000000000000000000 : ℝ)^512 ≤ (10006676410623079/10000000000000000 : ℝ)^2103 := by
      have hnat : (25068593174929559401 : ℕ)^512*10000000000000000^2103 ≤ 10006676410623079^2103*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25068593174929559401 25000000000000000000 10006676410623079 10000000000000000 512 2103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006676410623079/10000000000000000 : ℝ)) (X := (25068593174929559401/25000000000000000000 : ℝ)) (by norm_num) 2103 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(63007378004537/6250000000000000000 : ℝ) ≤ ((7007021355785668339/7009000000000000000 : ℝ)+2*(3313661683197/1401800000000000 : ℝ)*(243/4000 : ℝ))^(2103/512 : ℝ) := by
    rw [show (7007021355785668339/7009000000000000000 : ℝ)+2*(3313661683197/1401800000000000 : ℝ)*(243/4000 : ℝ)=(2000009817451337/2000000000000000 : ℝ) by norm_num, show 1+2*(63007378004537/6250000000000000000 : ℝ)=(3125063007378004537/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(68593174929559401/50000000000000000000 : ℝ)+(63007378004537/6250000000000000000 : ℝ) ≤ ((7007021355785668339/7009000000000000000 : ℝ)+(3313661683197/1401800000000000 : ℝ)*((20093/100000 : ℝ)+(243/4000 : ℝ)))^(2103/512 : ℝ) := by
    rw [show (7007021355785668339/7009000000000000000 : ℝ)+(3313661683197/1401800000000000 : ℝ)*((20093/100000 : ℝ)+(243/4000 : ℝ))=(5001681374469941/5000000000000000 : ℝ) by norm_num, show 1+(68593174929559401/50000000000000000000 : ℝ)+(63007378004537/6250000000000000000 : ℝ)=(50069097233953595697/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(68593174929559401/50000000000000000000 : ℝ) ≤ ((7007021355785668339/7009000000000000000 : ℝ)+2*(3313661683197/1401800000000000 : ℝ)*(20093/100000 : ℝ))^(2103/512 : ℝ) := by
    rw [show (7007021355785668339/7009000000000000000 : ℝ)+2*(3313661683197/1401800000000000 : ℝ)*(20093/100000 : ℝ)=(10006676410623079/10000000000000000 : ℝ) by norm_num, show 1+2*(68593174929559401/50000000000000000000 : ℝ)=(25068593174929559401/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7007021355785668339/7009000000000000000 : ℝ)*(X 1 0+X 2 0)+(3313661683197/1401800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2103/512 : ℝ)) (lo := (243/4000 : ℝ)) (hi := (20093/100000 : ℝ)) (c := (7007021355785668339/7009000000000000000 : ℝ)) (alpha := (3313661683197/1401800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7007021355785668339/7009000000000000000 : ℝ)*(X 0 1+X 2 1)+(3313661683197/1401800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2103/512 : ℝ)) (lo := (243/4000 : ℝ)) (hi := (20093/100000 : ℝ)) (c := (7007021355785668339/7009000000000000000 : ℝ)) (alpha := (3313661683197/1401800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7007021355785668339/7009000000000000000 : ℝ)*(X 0 2+X 1 2)+(3313661683197/1401800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2103/512 : ℝ)) (lo := (243/4000 : ℝ)) (hi := (20093/100000 : ℝ)) (c := (7007021355785668339/7009000000000000000 : ℝ)) (alpha := (3313661683197/1401800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2115528499/10000000000 : ℝ)*X 0 0+(549658997/1000000000 : ℝ)*X 0 1+(5171429807/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5370586859/10000000000 : ℝ)*X 1 0+(-285511237/1250000000 : ℝ)*X 1 1+(258571487/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2685293331/5000000000 : ℝ)*X 2 0+(1034285983/2000000000 : ℝ)*X 2 1+(-285511241/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((173786551/400000000 : ℝ)*X 0 0+(2014170331/5000000000 : ℝ)*X 0 1+(2342575209/5000000000 : ℝ)*X 0 2+(173786551/400000000 : ℝ)*X 1 0+(2014170331/5000000000 : ℝ)*X 1 1+(2342575209/5000000000 : ℝ)*X 1 2+(173786551/400000000 : ℝ)*X 2 0+(2014170331/5000000000 : ℝ)*X 2 1+(2342575209/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-528902909/2500000000 : ℝ)*X 0 0+(5173552339/10000000000 : ℝ)*X 0 1+(2747223629/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((330479001/625000000 : ℝ)*X 1 0+(-98053611/500000000 : ℝ)*X 1 1+(5494447293/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2643832099/5000000000 : ℝ)*X 2 0+(2747223669/5000000000 : ℝ)*X 2 1+(-1961071907/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4344831187/10000000000 : ℝ)*X 0 0+(936172623/2000000000 : ℝ)*X 0 1+(4032668527/10000000000 : ℝ)*X 0 2+(4344831187/10000000000 : ℝ)*X 1 0+(936172623/2000000000 : ℝ)*X 1 1+(4032668527/10000000000 : ℝ)*X 1 2+(4344831187/10000000000 : ℝ)*X 2 0+(936172623/2000000000 : ℝ)*X 2 1+(4032668527/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (681696918196905807631793277/175225000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (77342587/10000000000000 : ℝ)*(base19) + (150184033/25000000000000 : ℝ)*(base23) + (4019839/12500000000000 : ℝ)*(lower2) + (35707697/25000000000000 : ℝ)*(upper3) + (4659871/10000000000000 : ℝ)*(upper5) + (1149485397619219/50000000000000 : ℝ)*(major0) + (1149485397619219/50000000000000 : ℝ)*(major1) + (1149485397619219/50000000000000 : ℝ)*(major2) + (768853988622571/25000000000000 : ℝ)*(sp0) + (1537710841409149/50000000000000 : ℝ)*(sp1) + (768855463877009/25000000000000 : ℝ)*(sp2) + (761257278010109/50000000000000 : ℝ)*(sp3) + (6501753883/100000000000000 : ℝ)*(sp4) + (556066523/12500000000000 : ℝ)*(sp7) + (761259502276201/50000000000000 : ℝ)*(f.failure) + (384427807030521/12500000000000 : ℝ)*(f.sum) + (170926477084287/35045000000000000000000000000 : ℝ)*base66 + (2779252902530072241/350450000000000000000000000000000 : ℝ)*base67 + (1866579191319622241/350450000000000000000000000000000 : ℝ)*base69 + (1620230628058922241/350450000000000000000000000000000 : ℝ)*base71 + (141094119937917/35045000000000000000000000000 : ℝ)*base74 + (1106528048013477759/350450000000000000000000000000000 : ℝ)*base76 + (2603347160873577759/350450000000000000000000000000000 : ℝ)*base78 + (1237461051074722241/350450000000000000000000000000000 : ℝ)*base79 + (15565811197637/35045000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (32129639/5000000000000000000000 : ℝ)*base89 + (32129639/5000000000000000000000 : ℝ)*base91 + (32129639/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (865066350798459608573655747/87612500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2349348353/100000000000000 : ℝ)*(base19) + (159057411/6250000000000 : ℝ)*(base23) + (6002993/100000000000000 : ℝ)*(upper2) + (11980723/4000000000000 : ℝ)*(upper3) + (199145123/100000000000000 : ℝ)*(upper5) + (582378961487309/25000000000000 : ℝ)*(major0) + (582378961487309/25000000000000 : ℝ)*(major1) + (582378961487309/25000000000000 : ℝ)*(major2) + (2979328031/12500000000000 : ℝ)*(sp1) + (7185481587/25000000000000 : ℝ)*(sp2) + (3116283558316061/100000000000000 : ℝ)*(sp4) + (155812868717173/5000000000000 : ℝ)*(sp5) + (3116252271471137/100000000000000 : ℝ)*(sp6) + (385686951114121/25000000000000 : ℝ)*(sp7) + (385686951114121/25000000000000 : ℝ)*(f.failure) + (3116283558316061/100000000000000 : ℝ)*(f.sum) + (42138450270853/17522500000000000000000000000 : ℝ)*base65 + (315030623964699751/175225000000000000000000000000000 : ℝ)*base67 + (1147492100509624751/175225000000000000000000000000000 : ℝ)*base69 + (195304226486525249/175225000000000000000000000000000 : ℝ)*base72 + (2891352798797/17522500000000000000000000000 : ℝ)*base74 + (302420726983174751/175225000000000000000000000000000 : ℝ)*base75 + (1192139394763724751/175225000000000000000000000000000 : ℝ)*base77 + (126460511845875249/175225000000000000000000000000000 : ℝ)*base80 + (77235408464821/35045000000000000000000000000 : ℝ)*base81 + (13384519/2500000000000000000000 : ℝ)*base89 + (13384519/2500000000000000000000 : ℝ)*base91 + (13384519/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1220_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150997839/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (243/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9409/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8141/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1220_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1220_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150997839/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9409/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8141/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1220_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1220_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1220_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150997839/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9409/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8141/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1220_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

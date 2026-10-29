-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1584_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:30:51.767607+00:00
-- url     : https://prove2.me/submissions/5e236cbe-e316-4274-833d-fe67249c5e30

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
theorem support_rectangle_w1584_s6_0 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334207589/625000000 : ℝ)*x 0 + (1305129421/2500000000 : ℝ)*x 1 + (-935372407/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334207589/625000000 : ℝ)^4665 ≤ (44841171987369/100000000000000 : ℝ)^3641 := by
    have hnat : (334207589 : ℕ)^4665*100000000000000^3641 ≤ 44841171987369^3641*625000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334207589 625000000 44841171987369 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1305129421/2500000000 : ℝ)^4665 ≤ (339713625547/781250000000 : ℝ)^3641 := by
    have hnat : (1305129421 : ℕ)^4665*781250000000^3641 ≤ 339713625547^3641*2500000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305129421 2500000000 339713625547 781250000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (935372407/5000000000 : ℝ)^4665 ≤ (5837741963413/50000000000000 : ℝ)^3641 := by
    have hnat : (935372407 : ℕ)^4665*50000000000000^3641 ≤ 5837741963413^3641*5000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      935372407 5000000000 5837741963413 50000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334207589/625000000 : ℝ), (1305129421/2500000000 : ℝ), (-935372407/5000000000 : ℝ)] ![(44841171987369/100000000000000 : ℝ), (339713625547/781250000000 : ℝ), (5837741963413/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334207589/625000000 : ℝ)|^4665 ≤ (44841171987369/100000000000000 : ℝ)^3641
        have hw : |(334207589/625000000 : ℝ)|=(334207589/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1305129421/2500000000 : ℝ)|^4665 ≤ (339713625547/781250000000 : ℝ)^3641
        have hw : |(1305129421/2500000000 : ℝ)|=(1305129421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-935372407/5000000000 : ℝ)|^4665 ≤ (5837741963413/50000000000000 : ℝ)^3641
        have hw : |(-935372407/5000000000 : ℝ)|=(935372407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s6_1 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-883345283/5000000000 : ℝ)*x 0 + (5221580459/10000000000 : ℝ)*x 1 + (5422944413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (883345283/5000000000 : ℝ)^4665 ≤ (1356253438399/12500000000000 : ℝ)^3641 := by
    have hnat : (883345283 : ℕ)^4665*12500000000000^3641 ≤ 1356253438399^3641*5000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883345283 5000000000 1356253438399 12500000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5221580459/10000000000 : ℝ)^4665 ≤ (43494686186299/100000000000000 : ℝ)^3641 := by
    have hnat : (5221580459 : ℕ)^4665*100000000000000^3641 ≤ 43494686186299^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221580459 10000000000 43494686186299 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422944413/10000000000 : ℝ)^4665 ≤ (45655286297977/100000000000000 : ℝ)^3641 := by
    have hnat : (5422944413 : ℕ)^4665*100000000000000^3641 ≤ 45655286297977^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422944413 10000000000 45655286297977 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-883345283/5000000000 : ℝ), (5221580459/10000000000 : ℝ), (5422944413/10000000000 : ℝ)] ![(1356253438399/12500000000000 : ℝ), (43494686186299/100000000000000 : ℝ), (45655286297977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-883345283/5000000000 : ℝ)|^4665 ≤ (1356253438399/12500000000000 : ℝ)^3641
        have hw : |(-883345283/5000000000 : ℝ)|=(883345283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5221580459/10000000000 : ℝ)|^4665 ≤ (43494686186299/100000000000000 : ℝ)^3641
        have hw : |(5221580459/10000000000 : ℝ)|=(5221580459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422944413/10000000000 : ℝ)|^4665 ≤ (45655286297977/100000000000000 : ℝ)^3641
        have hw : |(5422944413/10000000000 : ℝ)|=(5422944413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s6_2 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293395197/10000000000 : ℝ)*x 0 + (-834158939/5000000000 : ℝ)*x 1 + (5422944401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293395197/10000000000 : ℝ)^4665 ≤ (44262604727459/100000000000000 : ℝ)^3641 := by
    have hnat : (5293395197 : ℕ)^4665*100000000000000^3641 ≤ 44262604727459^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293395197 10000000000 44262604727459 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (834158939/5000000000 : ℝ)^4665 ≤ (10082109093219/100000000000000 : ℝ)^3641 := by
    have hnat : (834158939 : ℕ)^4665*100000000000000^3641 ≤ 10082109093219^3641*5000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834158939 5000000000 10082109093219 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422944401/10000000000 : ℝ)^4665 ≤ (45655286168537/100000000000000 : ℝ)^3641 := by
    have hnat : (5422944401 : ℕ)^4665*100000000000000^3641 ≤ 45655286168537^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422944401 10000000000 45655286168537 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293395197/10000000000 : ℝ), (-834158939/5000000000 : ℝ), (5422944401/10000000000 : ℝ)] ![(44262604727459/100000000000000 : ℝ), (10082109093219/100000000000000 : ℝ), (45655286168537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293395197/10000000000 : ℝ)|^4665 ≤ (44262604727459/100000000000000 : ℝ)^3641
        have hw : |(5293395197/10000000000 : ℝ)|=(5293395197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-834158939/5000000000 : ℝ)|^4665 ≤ (10082109093219/100000000000000 : ℝ)^3641
        have hw : |(-834158939/5000000000 : ℝ)|=(834158939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422944401/10000000000 : ℝ)|^4665 ≤ (45655286168537/100000000000000 : ℝ)^3641
        have hw : |(5422944401/10000000000 : ℝ)|=(5422944401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s6_3 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293395189/10000000000 : ℝ)*x 0 + (2711472209/5000000000 : ℝ)*x 1 + (-333663573/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293395189/10000000000 : ℝ)^4665 ≤ (177050418567/400000000000 : ℝ)^3641 := by
    have hnat : (5293395189 : ℕ)^4665*400000000000^3641 ≤ 177050418567^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293395189 10000000000 177050418567 400000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2711472209/5000000000 : ℝ)^4665 ≤ (4565528635191/10000000000000 : ℝ)^3641 := by
    have hnat : (2711472209 : ℕ)^4665*10000000000000^3641 ≤ 4565528635191^3641*5000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711472209 5000000000 4565528635191 10000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (333663573/2000000000 : ℝ)^4665 ≤ (5041054496281/50000000000000 : ℝ)^3641 := by
    have hnat : (333663573 : ℕ)^4665*50000000000000^3641 ≤ 5041054496281^3641*2000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      333663573 2000000000 5041054496281 50000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293395189/10000000000 : ℝ), (2711472209/5000000000 : ℝ), (-333663573/2000000000 : ℝ)] ![(177050418567/400000000000 : ℝ), (4565528635191/10000000000000 : ℝ), (5041054496281/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293395189/10000000000 : ℝ)|^4665 ≤ (177050418567/400000000000 : ℝ)^3641
        have hw : |(5293395189/10000000000 : ℝ)|=(5293395189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2711472209/5000000000 : ℝ)|^4665 ≤ (4565528635191/10000000000000 : ℝ)^3641
        have hw : |(2711472209/5000000000 : ℝ)|=(2711472209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-333663573/2000000000 : ℝ)|^4665 ≤ (5041054496281/50000000000000 : ℝ)^3641
        have hw : |(-333663573/2000000000 : ℝ)|=(333663573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s6_4 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (423744453/1000000000 : ℝ)*x 0 + (1120720533/2500000000 : ℝ)*x 1 + (4003013319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (423744453/1000000000 : ℝ)^4665 ≤ (6656719079461/20000000000000 : ℝ)^3641 := by
    have hnat : (423744453 : ℕ)^4665*20000000000000^3641 ≤ 6656719079461^3641*1000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423744453 1000000000 6656719079461 20000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1120720533/2500000000 : ℝ)^4665 ≤ (7154689694059/20000000000000 : ℝ)^3641 := by
    have hnat : (1120720533 : ℕ)^4665*20000000000000^3641 ≤ 7154689694059^3641*2500000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120720533 2500000000 7154689694059 20000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4003013319/10000000000 : ℝ)^4665 ≤ (7735739028531/25000000000000 : ℝ)^3641 := by
    have hnat : (4003013319 : ℕ)^4665*25000000000000^3641 ≤ 7735739028531^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4003013319 10000000000 7735739028531 25000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(423744453/1000000000 : ℝ), (1120720533/2500000000 : ℝ), (4003013319/10000000000 : ℝ)] ![(6656719079461/20000000000000 : ℝ), (7154689694059/20000000000000 : ℝ), (7735739028531/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(423744453/1000000000 : ℝ)|^4665 ≤ (6656719079461/20000000000000 : ℝ)^3641
        have hw : |(423744453/1000000000 : ℝ)|=(423744453/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1120720533/2500000000 : ℝ)|^4665 ≤ (7154689694059/20000000000000 : ℝ)^3641
        have hw : |(1120720533/2500000000 : ℝ)|=(1120720533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4003013319/10000000000 : ℝ)|^4665 ≤ (7735739028531/25000000000000 : ℝ)^3641
        have hw : |(4003013319/10000000000 : ℝ)|=(4003013319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1584_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169154589/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5583/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5583/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15483/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5583/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5583/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5583/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5583/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5583/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5583/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5583/50000 : ℝ) ^ (4663/1024 : ℝ) ≤ (461743716915409/10000000000000000000 : ℝ) := by
    have hpowers : (5583/50000 : ℝ)^4663 ≤ (461743716915409/10000000000000000000 : ℝ)^1024 := by
      have hnat : (5583 : ℕ)^4663*10000000000000000000^1024 ≤ 461743716915409^1024*50000^4663 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5583 50000 461743716915409 10000000000000000000 4663 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5583/50000 : ℝ)) (X := (461743716915409/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3871/25000 : ℝ) ^ (4663/1024 : ℝ) ≤ (10231330208688101/50000000000000000000 : ℝ) := by
    have hpowers : (3871/25000 : ℝ)^4663 ≤ (10231330208688101/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3871 : ℕ)^4663*50000000000000000000^1024 ≤ 10231330208688101^1024*25000^4663 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3871 25000 10231330208688101 50000000000000000000 4663 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3871/25000 : ℝ)) (X := (10231330208688101/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000461743716915409/5000000000000000000 : ℝ) ≤ (10000202791562967/10000000000000000 : ℝ) ^ (4663/1024 : ℝ) := by
    have hpowers : (5000461743716915409/5000000000000000000 : ℝ)^1024 ≤ (10000202791562967/10000000000000000 : ℝ)^4663 := by
      have hnat : (5000461743716915409 : ℕ)^1024*10000000000000000^4663 ≤ 10000202791562967^4663*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000461743716915409 5000000000000000000 10000202791562967 10000000000000000 1024 4663 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000202791562967/10000000000000000 : ℝ)) (X := (5000461743716915409/5000000000000000000 : ℝ)) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25006270024396632573/25000000000000000000 : ℝ) ≤ (312517209620281/312500000000000 : ℝ) ^ (4663/1024 : ℝ) := by
    have hpowers : (25006270024396632573/25000000000000000000 : ℝ)^1024 ≤ (312517209620281/312500000000000 : ℝ)^4663 := by
      have hnat : (25006270024396632573 : ℕ)^1024*312500000000000^4663 ≤ 312517209620281^4663*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006270024396632573 25000000000000000000 312517209620281 312500000000000 1024 4663 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312517209620281/312500000000000 : ℝ)) (X := (25006270024396632573/25000000000000000000 : ℝ)) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25010231330208688101/25000000000000000000 : ℝ) ≤ (10000898624135017/10000000000000000 : ℝ) ^ (4663/1024 : ℝ) := by
    have hpowers : (25010231330208688101/25000000000000000000 : ℝ)^1024 ≤ (10000898624135017/10000000000000000 : ℝ)^4663 := by
      have hnat : (25010231330208688101 : ℕ)^1024*10000000000000000^4663 ≤ 10000898624135017^4663*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010231330208688101 25000000000000000000 10000898624135017 10000000000000000 1024 4663 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000898624135017/10000000000000000 : ℝ)) (X := (25010231330208688101/25000000000000000000 : ℝ)) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(461743716915409/10000000000000000000 : ℝ) ≤ ((21586552993734690603/21590000000000000000 : ℝ)+2*(13916651441/17272000000000 : ℝ)*(5583/50000 : ℝ))^(4663/1024 : ℝ) := by
    rw [show (21586552993734690603/21590000000000000000 : ℝ)+2*(13916651441/17272000000000 : ℝ)*(5583/50000 : ℝ)=(10000202791562967/10000000000000000 : ℝ) by norm_num, show 1+2*(461743716915409/10000000000000000000 : ℝ)=(5000461743716915409/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10231330208688101/50000000000000000000 : ℝ)+(461743716915409/10000000000000000000 : ℝ) ≤ ((21586552993734690603/21590000000000000000 : ℝ)+(13916651441/17272000000000 : ℝ)*((3871/25000 : ℝ)+(5583/50000 : ℝ)))^(4663/1024 : ℝ) := by
    rw [show (21586552993734690603/21590000000000000000 : ℝ)+(13916651441/17272000000000 : ℝ)*((3871/25000 : ℝ)+(5583/50000 : ℝ))=(312517209620281/312500000000000 : ℝ) by norm_num, show 1+(10231330208688101/50000000000000000000 : ℝ)+(461743716915409/10000000000000000000 : ℝ)=(25006270024396632573/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10231330208688101/50000000000000000000 : ℝ) ≤ ((21586552993734690603/21590000000000000000 : ℝ)+2*(13916651441/17272000000000 : ℝ)*(3871/25000 : ℝ))^(4663/1024 : ℝ) := by
    rw [show (21586552993734690603/21590000000000000000 : ℝ)+2*(13916651441/17272000000000 : ℝ)*(3871/25000 : ℝ)=(10000898624135017/10000000000000000 : ℝ) by norm_num, show 1+2*(10231330208688101/50000000000000000000 : ℝ)=(25010231330208688101/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21586552993734690603/21590000000000000000 : ℝ)*(X 1 0+X 2 0)+(13916651441/17272000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4663/1024 : ℝ)) (lo := (5583/50000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (21586552993734690603/21590000000000000000 : ℝ)) (alpha := (13916651441/17272000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21586552993734690603/21590000000000000000 : ℝ)*(X 0 1+X 2 1)+(13916651441/17272000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4663/1024 : ℝ)) (lo := (5583/50000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (21586552993734690603/21590000000000000000 : ℝ)) (alpha := (13916651441/17272000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21586552993734690603/21590000000000000000 : ℝ)*(X 0 2+X 1 2)+(13916651441/17272000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4663/1024 : ℝ)) (lo := (5583/50000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (21586552993734690603/21590000000000000000 : ℝ)) (alpha := (13916651441/17272000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((334207589/625000000 : ℝ)*X 2 0+(1305129421/2500000000 : ℝ)*X 2 1+(-935372407/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s6_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-883345283/5000000000 : ℝ)*X 0 0+(5221580459/10000000000 : ℝ)*X 0 1+(5422944413/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s6_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5293395197/10000000000 : ℝ)*X 1 0+(-834158939/5000000000 : ℝ)*X 1 1+(5422944401/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s6_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5293395189/10000000000 : ℝ)*X 2 0+(2711472209/5000000000 : ℝ)*X 2 1+(-333663573/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s6_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((423744453/1000000000 : ℝ)*X 0 0+(1120720533/2500000000 : ℝ)*X 0 1+(4003013319/10000000000 : ℝ)*X 0 2+(423744453/1000000000 : ℝ)*X 1 0+(1120720533/2500000000 : ℝ)*X 1 1+(4003013319/10000000000 : ℝ)*X 1 2+(423744453/1000000000 : ℝ)*X 2 0+(1120720533/2500000000 : ℝ)*X 2 1+(4003013319/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s6_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (386535772305652477125753477/107950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (276928837/50000000000000 : ℝ)*(base19) + (75609521/12500000000000 : ℝ)*(base23) + (85056869/50000000000000 : ℝ)*(lower1) + (77430641/100000000000000 : ℝ)*(upper3) + (1227529/5000000000000 : ℝ)*(lower4) + (72411849/100000000000000 : ℝ)*(upper5) + (352501120413547/10000000000000 : ℝ)*(major0) + (352501120413547/10000000000000 : ℝ)*(major1) + (352501120413547/10000000000000 : ℝ)*(major2) + (596038749/50000000000000 : ℝ)*(sp0) + (1241530760818769/25000000000000 : ℝ)*(sp1) + (4966122489417403/100000000000000 : ℝ)*(sp2) + (4966121246321411/100000000000000 : ℝ)*(sp3) + (83355969825577/4000000000000 : ℝ)*(sp4) + (83355969825577/4000000000000 : ℝ)*(f.failure) + (1241530760818769/25000000000000 : ℝ)*(f.sum) + (9383684817469/2159000000000000000000000000 : ℝ)*base65 + (329562533342948841/215900000000000000000000000000000 : ℝ)*base67 + (2213709315676848841/215900000000000000000000000000000 : ℝ)*base69 + (4407564928896648841/215900000000000000000000000000000 : ℝ)*base71 + (5106575450619/2159000000000000000000000000 : ℝ)*base74 + (20830260644741651159/215900000000000000000000000000000 : ℝ)*base76 + (59491446599351159/215900000000000000000000000000000 : ℝ)*base78 + (411503374261548841/215900000000000000000000000000000 : ℝ)*base79 + (5442462786717/2159000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (877147/400000000000000000000 : ℝ)*base90 + (877147/400000000000000000000 : ℝ)*base92 + (877147/400000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1584_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169154589/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5583/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5583/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1584_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1584_box_0 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1565080759/10000000000 : ℝ)*x 0 + (5395093841/10000000000 : ℝ)*x 1 + (2697547189/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1565080759/10000000000 : ℝ)^4665 ≤ (9289816317373/100000000000000 : ℝ)^3641 := by
    have hnat : (1565080759 : ℕ)^4665*100000000000000^3641 ≤ 9289816317373^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1565080759 10000000000 9289816317373 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395093841/10000000000 : ℝ)^4665 ≤ (45355088940541/100000000000000 : ℝ)^3641 := by
    have hnat : (5395093841 : ℕ)^4665*100000000000000^3641 ≤ 45355088940541^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395093841 10000000000 45355088940541 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697547189/5000000000 : ℝ)^4665 ≤ (22677547362297/50000000000000 : ℝ)^3641 := by
    have hnat : (2697547189 : ℕ)^4665*50000000000000^3641 ≤ 22677547362297^3641*5000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697547189 5000000000 22677547362297 50000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1565080759/10000000000 : ℝ), (5395093841/10000000000 : ℝ), (2697547189/5000000000 : ℝ)] ![(9289816317373/100000000000000 : ℝ), (45355088940541/100000000000000 : ℝ), (22677547362297/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1565080759/10000000000 : ℝ)|^4665 ≤ (9289816317373/100000000000000 : ℝ)^3641
        have hw : |(-1565080759/10000000000 : ℝ)|=(1565080759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395093841/10000000000 : ℝ)|^4665 ≤ (45355088940541/100000000000000 : ℝ)^3641
        have hw : |(5395093841/10000000000 : ℝ)|=(5395093841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697547189/5000000000 : ℝ)|^4665 ≤ (22677547362297/50000000000000 : ℝ)^3641
        have hw : |(2697547189/5000000000 : ℝ)|=(2697547189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_box_1 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1317781899/2500000000 : ℝ)*x 0 + (-1737481241/10000000000 : ℝ)*x 1 + (1348773571/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1317781899/2500000000 : ℝ)^4665 ≤ (44024180816453/100000000000000 : ℝ)^3641 := by
    have hnat : (1317781899 : ℕ)^4665*100000000000000^3641 ≤ 44024180816453^3641*2500000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317781899 2500000000 44024180816453 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1737481241/10000000000 : ℝ)^4665 ≤ (10620725465941/100000000000000 : ℝ)^3641 := by
    have hnat : (1737481241 : ℕ)^4665*100000000000000^3641 ≤ 10620725465941^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1737481241 10000000000 10620725465941 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348773571/2500000000 : ℝ)^4665 ≤ (9071018742423/20000000000000 : ℝ)^3641 := by
    have hnat : (1348773571 : ℕ)^4665*20000000000000^3641 ≤ 9071018742423^3641*2500000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348773571 2500000000 9071018742423 20000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1317781899/2500000000 : ℝ), (-1737481241/10000000000 : ℝ), (1348773571/2500000000 : ℝ)] ![(44024180816453/100000000000000 : ℝ), (10620725465941/100000000000000 : ℝ), (9071018742423/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1317781899/2500000000 : ℝ)|^4665 ≤ (44024180816453/100000000000000 : ℝ)^3641
        have hw : |(1317781899/2500000000 : ℝ)|=(1317781899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1737481241/10000000000 : ℝ)|^4665 ≤ (10620725465941/100000000000000 : ℝ)^3641
        have hw : |(-1737481241/10000000000 : ℝ)|=(1737481241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348773571/2500000000 : ℝ)|^4665 ≤ (9071018742423/20000000000000 : ℝ)^3641
        have hw : |(1348773571/2500000000 : ℝ)|=(1348773571/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_box_2 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1317781873/2500000000 : ℝ)*x 0 + (5395094343/10000000000 : ℝ)*x 1 + (-1737481301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1317781873/2500000000 : ℝ)^4665 ≤ (44024179703563/100000000000000 : ℝ)^3641 := by
    have hnat : (1317781873 : ℕ)^4665*100000000000000^3641 ≤ 44024179703563^3641*2500000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317781873 2500000000 44024179703563 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395094343/10000000000 : ℝ)^4665 ≤ (45355094347607/100000000000000 : ℝ)^3641 := by
    have hnat : (5395094343 : ℕ)^4665*100000000000000^3641 ≤ 45355094347607^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395094343 10000000000 45355094347607 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1737481301/10000000000 : ℝ)^4665 ≤ (2655181483963/25000000000000 : ℝ)^3641 := by
    have hnat : (1737481301 : ℕ)^4665*25000000000000^3641 ≤ 2655181483963^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1737481301 10000000000 2655181483963 25000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1317781873/2500000000 : ℝ), (5395094343/10000000000 : ℝ), (-1737481301/10000000000 : ℝ)] ![(44024179703563/100000000000000 : ℝ), (45355094347607/100000000000000 : ℝ), (2655181483963/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1317781873/2500000000 : ℝ)|^4665 ≤ (44024179703563/100000000000000 : ℝ)^3641
        have hw : |(1317781873/2500000000 : ℝ)|=(1317781873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395094343/10000000000 : ℝ)|^4665 ≤ (45355094347607/100000000000000 : ℝ)^3641
        have hw : |(5395094343/10000000000 : ℝ)|=(5395094343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1737481301/10000000000 : ℝ)|^4665 ≤ (2655181483963/25000000000000 : ℝ)^3641
        have hw : |(-1737481301/10000000000 : ℝ)|=(1737481301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_box_3 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (277347637/625000000 : ℝ)*x 0 + (1035962447/2500000000 : ℝ)*x 1 + (828769963/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (277347637/625000000 : ℝ)^4665 ≤ (35310743206211/100000000000000 : ℝ)^3641 := by
    have hnat : (277347637 : ℕ)^4665*100000000000000^3641 ≤ 35310743206211^3641*625000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277347637 625000000 35310743206211 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035962447/2500000000 : ℝ)^4665 ≤ (16172314126439/50000000000000 : ℝ)^3641 := by
    have hnat : (1035962447 : ℕ)^4665*50000000000000^3641 ≤ 16172314126439^3641*2500000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035962447 2500000000 16172314126439 50000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (828769963/2000000000 : ℝ)^4665 ≤ (2021539282681/6250000000000 : ℝ)^3641 := by
    have hnat : (828769963 : ℕ)^4665*6250000000000^3641 ≤ 2021539282681^3641*2000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828769963 2000000000 2021539282681 6250000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(277347637/625000000 : ℝ), (1035962447/2500000000 : ℝ), (828769963/2000000000 : ℝ)] ![(35310743206211/100000000000000 : ℝ), (16172314126439/50000000000000 : ℝ), (2021539282681/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(277347637/625000000 : ℝ)|^4665 ≤ (35310743206211/100000000000000 : ℝ)^3641
        have hw : |(277347637/625000000 : ℝ)|=(277347637/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035962447/2500000000 : ℝ)|^4665 ≤ (16172314126439/50000000000000 : ℝ)^3641
        have hw : |(1035962447/2500000000 : ℝ)|=(1035962447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(828769963/2000000000 : ℝ)|^4665 ≤ (2021539282681/6250000000000 : ℝ)^3641
        have hw : |(828769963/2000000000 : ℝ)|=(828769963/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_box_4 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-123351899/625000000 : ℝ)*x 0 + (5245278211/10000000000 : ℝ)*x 1 + (5245278681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (123351899/625000000 : ℝ)^4665 ≤ (12504472726861/100000000000000 : ℝ)^3641 := by
    have hnat : (123351899 : ℕ)^4665*100000000000000^3641 ≤ 12504472726861^3641*625000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123351899 625000000 12504472726861 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245278211/10000000000 : ℝ)^4665 ≤ (34177938371/78125000000 : ℝ)^3641 := by
    have hnat : (5245278211 : ℕ)^4665*78125000000^3641 ≤ 34177938371^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245278211 10000000000 34177938371 78125000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245278681/10000000000 : ℝ)^4665 ≤ (5468470767167/12500000000000 : ℝ)^3641 := by
    have hnat : (5245278681 : ℕ)^4665*12500000000000^3641 ≤ 5468470767167^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245278681 10000000000 5468470767167 12500000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-123351899/625000000 : ℝ), (5245278211/10000000000 : ℝ), (5245278681/10000000000 : ℝ)] ![(12504472726861/100000000000000 : ℝ), (34177938371/78125000000 : ℝ), (5468470767167/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-123351899/625000000 : ℝ)|^4665 ≤ (12504472726861/100000000000000 : ℝ)^3641
        have hw : |(-123351899/625000000 : ℝ)|=(123351899/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245278211/10000000000 : ℝ)|^4665 ≤ (34177938371/78125000000 : ℝ)^3641
        have hw : |(5245278211/10000000000 : ℝ)|=(5245278211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245278681/10000000000 : ℝ)|^4665 ≤ (5468470767167/12500000000000 : ℝ)^3641
        have hw : |(5245278681/10000000000 : ℝ)|=(5245278681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_box_5 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5374869273/10000000000 : ℝ)*x 0 + (-1800258991/10000000000 : ℝ)*x 1 + (5245278761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374869273/10000000000 : ℝ)^4665 ≤ (45137364070263/100000000000000 : ℝ)^3641 := by
    have hnat : (5374869273 : ℕ)^4665*100000000000000^3641 ≤ 45137364070263^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374869273 10000000000 45137364070263 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1800258991/10000000000 : ℝ)^4665 ≤ (2778717230671/25000000000000 : ℝ)^3641 := by
    have hnat : (1800258991 : ℕ)^4665*25000000000000^3641 ≤ 2778717230671^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1800258991 10000000000 2778717230671 25000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245278761/10000000000 : ℝ)^4665 ≤ (21873883496111/50000000000000 : ℝ)^3641 := by
    have hnat : (5245278761 : ℕ)^4665*50000000000000^3641 ≤ 21873883496111^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245278761 10000000000 21873883496111 50000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374869273/10000000000 : ℝ), (-1800258991/10000000000 : ℝ), (5245278761/10000000000 : ℝ)] ![(45137364070263/100000000000000 : ℝ), (2778717230671/25000000000000 : ℝ), (21873883496111/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374869273/10000000000 : ℝ)|^4665 ≤ (45137364070263/100000000000000 : ℝ)^3641
        have hw : |(5374869273/10000000000 : ℝ)|=(5374869273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1800258991/10000000000 : ℝ)|^4665 ≤ (2778717230671/25000000000000 : ℝ)^3641
        have hw : |(-1800258991/10000000000 : ℝ)|=(1800258991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245278761/10000000000 : ℝ)|^4665 ≤ (21873883496111/50000000000000 : ℝ)^3641
        have hw : |(5245278761/10000000000 : ℝ)|=(5245278761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_box_6 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5374869463/10000000000 : ℝ)*x 0 + (5245278583/10000000000 : ℝ)*x 1 + (-1800258973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374869463/10000000000 : ℝ)^4665 ≤ (22568683057301/50000000000000 : ℝ)^3641 := by
    have hnat : (5374869463 : ℕ)^4665*50000000000000^3641 ≤ 22568683057301^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374869463 10000000000 22568683057301 50000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245278583/10000000000 : ℝ)^4665 ≤ (43747765090101/100000000000000 : ℝ)^3641 := by
    have hnat : (5245278583 : ℕ)^4665*100000000000000^3641 ≤ 43747765090101^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245278583 10000000000 43747765090101 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1800258973/10000000000 : ℝ)^4665 ≤ (1389358597537/12500000000000 : ℝ)^3641 := by
    have hnat : (1800258973 : ℕ)^4665*12500000000000^3641 ≤ 1389358597537^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1800258973 10000000000 1389358597537 12500000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374869463/10000000000 : ℝ), (5245278583/10000000000 : ℝ), (-1800258973/10000000000 : ℝ)] ![(22568683057301/50000000000000 : ℝ), (43747765090101/100000000000000 : ℝ), (1389358597537/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374869463/10000000000 : ℝ)|^4665 ≤ (22568683057301/50000000000000 : ℝ)^3641
        have hw : |(5374869463/10000000000 : ℝ)|=(5374869463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245278583/10000000000 : ℝ)|^4665 ≤ (43747765090101/100000000000000 : ℝ)^3641
        have hw : |(5245278583/10000000000 : ℝ)|=(5245278583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1800258973/10000000000 : ℝ)|^4665 ≤ (1389358597537/12500000000000 : ℝ)^3641
        have hw : |(-1800258973/10000000000 : ℝ)|=(1800258973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_box_7 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1008612243/2500000000 : ℝ)*x 0 + (869056061/2000000000 : ℝ)*x 1 + (4345280623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1008612243/2500000000 : ℝ)^4665 ≤ (31254634472321/100000000000000 : ℝ)^3641 := by
    have hnat : (1008612243 : ℕ)^4665*100000000000000^3641 ≤ 31254634472321^3641*2500000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008612243 2500000000 31254634472321 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (869056061/2000000000 : ℝ)^4665 ≤ (6874536229/20000000000 : ℝ)^3641 := by
    have hnat : (869056061 : ℕ)^4665*20000000000^3641 ≤ 6874536229^3641*2000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869056061 2000000000 6874536229 20000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4345280623/10000000000 : ℝ)^4665 ≤ (34372684367951/100000000000000 : ℝ)^3641 := by
    have hnat : (4345280623 : ℕ)^4665*100000000000000^3641 ≤ 34372684367951^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4345280623 10000000000 34372684367951 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1008612243/2500000000 : ℝ), (869056061/2000000000 : ℝ), (4345280623/10000000000 : ℝ)] ![(31254634472321/100000000000000 : ℝ), (6874536229/20000000000 : ℝ), (34372684367951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1008612243/2500000000 : ℝ)|^4665 ≤ (31254634472321/100000000000000 : ℝ)^3641
        have hw : |(1008612243/2500000000 : ℝ)|=(1008612243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(869056061/2000000000 : ℝ)|^4665 ≤ (6874536229/20000000000 : ℝ)^3641
        have hw : |(869056061/2000000000 : ℝ)|=(869056061/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4345280623/10000000000 : ℝ)|^4665 ≤ (34372684367951/100000000000000 : ℝ)^3641
        have hw : |(4345280623/10000000000 : ℝ)|=(4345280623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_box_8 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-235871937/1250000000 : ℝ)*x 0 + (5139585343/10000000000 : ℝ)*x 1 + (5415317811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (235871937/1250000000 : ℝ)^4665 ≤ (5902714005553/50000000000000 : ℝ)^3641 := by
    have hnat : (235871937 : ℕ)^4665*50000000000000^3641 ≤ 5902714005553^3641*1250000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235871937 1250000000 5902714005553 50000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5139585343/10000000000 : ℝ)^4665 ≤ (42621534940657/100000000000000 : ℝ)^3641 := by
    have hnat : (5139585343 : ℕ)^4665*100000000000000^3641 ≤ 42621534940657^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5139585343 10000000000 42621534940657 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415317811/10000000000 : ℝ)^4665 ≤ (11393259257329/25000000000000 : ℝ)^3641 := by
    have hnat : (5415317811 : ℕ)^4665*25000000000000^3641 ≤ 11393259257329^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415317811 10000000000 11393259257329 25000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-235871937/1250000000 : ℝ), (5139585343/10000000000 : ℝ), (5415317811/10000000000 : ℝ)] ![(5902714005553/50000000000000 : ℝ), (42621534940657/100000000000000 : ℝ), (11393259257329/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-235871937/1250000000 : ℝ)|^4665 ≤ (5902714005553/50000000000000 : ℝ)^3641
        have hw : |(-235871937/1250000000 : ℝ)|=(235871937/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5139585343/10000000000 : ℝ)|^4665 ≤ (42621534940657/100000000000000 : ℝ)^3641
        have hw : |(5139585343/10000000000 : ℝ)|=(5139585343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415317811/10000000000 : ℝ)|^4665 ≤ (11393259257329/25000000000000 : ℝ)^3641
        have hw : |(5415317811/10000000000 : ℝ)|=(5415317811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_box_9 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257120807/10000000000 : ℝ)*x 0 + (-432194609/2500000000 : ℝ)*x 1 + (135382937/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257120807/10000000000 : ℝ)^4665 ≤ (43874352156649/100000000000000 : ℝ)^3641 := by
    have hnat : (5257120807 : ℕ)^4665*100000000000000^3641 ≤ 43874352156649^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257120807 10000000000 43874352156649 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (432194609/2500000000 : ℝ)^4665 ≤ (10552614363599/100000000000000 : ℝ)^3641 := by
    have hnat : (432194609 : ℕ)^4665*100000000000000^3641 ≤ 10552614363599^3641*2500000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432194609 2500000000 10552614363599 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135382937/250000000 : ℝ)^4665 ≤ (22786516730173/50000000000000 : ℝ)^3641 := by
    have hnat : (135382937 : ℕ)^4665*50000000000000^3641 ≤ 22786516730173^3641*250000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135382937 250000000 22786516730173 50000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257120807/10000000000 : ℝ), (-432194609/2500000000 : ℝ), (135382937/250000000 : ℝ)] ![(43874352156649/100000000000000 : ℝ), (10552614363599/100000000000000 : ℝ), (22786516730173/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257120807/10000000000 : ℝ)|^4665 ≤ (43874352156649/100000000000000 : ℝ)^3641
        have hw : |(5257120807/10000000000 : ℝ)|=(5257120807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-432194609/2500000000 : ℝ)|^4665 ≤ (10552614363599/100000000000000 : ℝ)^3641
        have hw : |(-432194609/2500000000 : ℝ)|=(432194609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135382937/250000000 : ℝ)|^4665 ≤ (22786516730173/50000000000000 : ℝ)^3641
        have hw : |(135382937/250000000 : ℝ)|=(135382937/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_box_10 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628560151/5000000000 : ℝ)*x 0 + (2707659129/5000000000 : ℝ)*x 1 + (-345755611/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628560151/5000000000 : ℝ)^4665 ≤ (10968586689189/25000000000000 : ℝ)^3641 := by
    have hnat : (2628560151 : ℕ)^4665*25000000000000^3641 ≤ 10968586689189^3641*5000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628560151 5000000000 10968586689189 25000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707659129/5000000000 : ℝ)^4665 ≤ (11393260462261/25000000000000 : ℝ)^3641 := by
    have hnat : (2707659129 : ℕ)^4665*25000000000000^3641 ≤ 11393260462261^3641*5000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707659129 5000000000 11393260462261 25000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (345755611/2000000000 : ℝ)^4665 ≤ (10552611383871/100000000000000 : ℝ)^3641 := by
    have hnat : (345755611 : ℕ)^4665*100000000000000^3641 ≤ 10552611383871^3641*2000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345755611 2000000000 10552611383871 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628560151/5000000000 : ℝ), (2707659129/5000000000 : ℝ), (-345755611/2000000000 : ℝ)] ![(10968586689189/25000000000000 : ℝ), (11393260462261/25000000000000 : ℝ), (10552611383871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628560151/5000000000 : ℝ)|^4665 ≤ (10968586689189/25000000000000 : ℝ)^3641
        have hw : |(2628560151/5000000000 : ℝ)|=(2628560151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707659129/5000000000 : ℝ)|^4665 ≤ (11393260462261/25000000000000 : ℝ)^3641
        have hw : |(2707659129/5000000000 : ℝ)|=(2707659129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-345755611/2000000000 : ℝ)|^4665 ≤ (10552611383871/100000000000000 : ℝ)^3641
        have hw : |(-345755611/2000000000 : ℝ)|=(345755611/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_box_11 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4490835949/10000000000 : ℝ)*x 0 + (2058311857/5000000000 : ℝ)*x 1 + (4116624359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4490835949/10000000000 : ℝ)^4665 ≤ (7170958225183/20000000000000 : ℝ)^3641 := by
    have hnat : (4490835949 : ℕ)^4665*20000000000000^3641 ≤ 7170958225183^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490835949 10000000000 7170958225183 20000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2058311857/5000000000 : ℝ)^4665 ≤ (8018150302483/25000000000000 : ℝ)^3641 := by
    have hnat : (2058311857 : ℕ)^4665*25000000000000^3641 ≤ 8018150302483^3641*5000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2058311857 5000000000 8018150302483 25000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4116624359/10000000000 : ℝ)^4665 ≤ (32072607648417/100000000000000 : ℝ)^3641 := by
    have hnat : (4116624359 : ℕ)^4665*100000000000000^3641 ≤ 32072607648417^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4116624359 10000000000 32072607648417 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4490835949/10000000000 : ℝ), (2058311857/5000000000 : ℝ), (4116624359/10000000000 : ℝ)] ![(7170958225183/20000000000000 : ℝ), (8018150302483/25000000000000 : ℝ), (32072607648417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4490835949/10000000000 : ℝ)|^4665 ≤ (7170958225183/20000000000000 : ℝ)^3641
        have hw : |(4490835949/10000000000 : ℝ)|=(4490835949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2058311857/5000000000 : ℝ)|^4665 ≤ (8018150302483/25000000000000 : ℝ)^3641
        have hw : |(2058311857/5000000000 : ℝ)|=(2058311857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4116624359/10000000000 : ℝ)|^4665 ≤ (32072607648417/100000000000000 : ℝ)^3641
        have hw : |(4116624359/10000000000 : ℝ)|=(4116624359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_box_12 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-825667309/5000000000 : ℝ)*x 0 + (5497605483/10000000000 : ℝ)*x 1 + (5230229851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (825667309/5000000000 : ℝ)^4665 ≤ (4975399070189/50000000000000 : ℝ)^3641 := by
    have hnat : (825667309 : ℕ)^4665*50000000000000^3641 ≤ 4975399070189^3641*5000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      825667309 5000000000 4975399070189 50000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5497605483/10000000000 : ℝ)^4665 ≤ (46462183727229/100000000000000 : ℝ)^3641 := by
    have hnat : (5497605483 : ℕ)^4665*100000000000000^3641 ≤ 46462183727229^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5497605483 10000000000 46462183727229 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5230229851/10000000000 : ℝ)^4665 ≤ (10896754527649/25000000000000 : ℝ)^3641 := by
    have hnat : (5230229851 : ℕ)^4665*25000000000000^3641 ≤ 10896754527649^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230229851 10000000000 10896754527649 25000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-825667309/5000000000 : ℝ), (5497605483/10000000000 : ℝ), (5230229851/10000000000 : ℝ)] ![(4975399070189/50000000000000 : ℝ), (46462183727229/100000000000000 : ℝ), (10896754527649/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-825667309/5000000000 : ℝ)|^4665 ≤ (4975399070189/50000000000000 : ℝ)^3641
        have hw : |(-825667309/5000000000 : ℝ)|=(825667309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5497605483/10000000000 : ℝ)|^4665 ≤ (46462183727229/100000000000000 : ℝ)^3641
        have hw : |(5497605483/10000000000 : ℝ)|=(5497605483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5230229851/10000000000 : ℝ)|^4665 ≤ (10896754527649/25000000000000 : ℝ)^3641
        have hw : |(5230229851/10000000000 : ℝ)|=(5230229851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_box_13 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5385291871/10000000000 : ℝ)*x 0 + (-903198317/5000000000 : ℝ)*x 1 + (1307557459/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5385291871/10000000000 : ℝ)^4665 ≤ (2828096151847/6250000000000 : ℝ)^3641 := by
    have hnat : (5385291871 : ℕ)^4665*6250000000000^3641 ≤ 2828096151847^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385291871 10000000000 2828096151847 6250000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (903198317/5000000000 : ℝ)^4665 ≤ (1116344360171/10000000000000 : ℝ)^3641 := by
    have hnat : (903198317 : ℕ)^4665*10000000000000^3641 ≤ 1116344360171^3641*5000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903198317 5000000000 1116344360171 10000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1307557459/2500000000 : ℝ)^4665 ≤ (8717403590087/20000000000000 : ℝ)^3641 := by
    have hnat : (1307557459 : ℕ)^4665*20000000000000^3641 ≤ 8717403590087^3641*2500000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307557459 2500000000 8717403590087 20000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5385291871/10000000000 : ℝ), (-903198317/5000000000 : ℝ), (1307557459/2500000000 : ℝ)] ![(2828096151847/6250000000000 : ℝ), (1116344360171/10000000000000 : ℝ), (8717403590087/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5385291871/10000000000 : ℝ)|^4665 ≤ (2828096151847/6250000000000 : ℝ)^3641
        have hw : |(5385291871/10000000000 : ℝ)|=(5385291871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-903198317/5000000000 : ℝ)|^4665 ≤ (1116344360171/10000000000000 : ℝ)^3641
        have hw : |(-903198317/5000000000 : ℝ)|=(903198317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1307557459/2500000000 : ℝ)|^4665 ≤ (8717403590087/20000000000000 : ℝ)^3641
        have hw : |(1307557459/2500000000 : ℝ)|=(1307557459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_box_14 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2692645921/5000000000 : ℝ)*x 0 + (2615114927/5000000000 : ℝ)*x 1 + (-36127933/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2692645921/5000000000 : ℝ)^4665 ≤ (5656192264669/12500000000000 : ℝ)^3641 := by
    have hnat : (2692645921 : ℕ)^4665*12500000000000^3641 ≤ 5656192264669^3641*5000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692645921 5000000000 5656192264669 12500000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2615114927/5000000000 : ℝ)^4665 ≤ (43587018142629/100000000000000 : ℝ)^3641 := by
    have hnat : (2615114927 : ℕ)^4665*100000000000000^3641 ≤ 43587018142629^3641*5000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615114927 5000000000 43587018142629 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (36127933/200000000 : ℝ)^4665 ≤ (5581721864199/50000000000000 : ℝ)^3641 := by
    have hnat : (36127933 : ℕ)^4665*50000000000000^3641 ≤ 5581721864199^3641*200000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36127933 200000000 5581721864199 50000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2692645921/5000000000 : ℝ), (2615114927/5000000000 : ℝ), (-36127933/200000000 : ℝ)] ![(5656192264669/12500000000000 : ℝ), (43587018142629/100000000000000 : ℝ), (5581721864199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2692645921/5000000000 : ℝ)|^4665 ≤ (5656192264669/12500000000000 : ℝ)^3641
        have hw : |(2692645921/5000000000 : ℝ)|=(2692645921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2615114927/5000000000 : ℝ)|^4665 ≤ (43587018142629/100000000000000 : ℝ)^3641
        have hw : |(2615114927/5000000000 : ℝ)|=(2615114927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-36127933/200000000 : ℝ)|^4665 ≤ (5581721864199/50000000000000 : ℝ)^3641
        have hw : |(-36127933/200000000 : ℝ)|=(36127933/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_box_15 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (99827317/250000000 : ℝ)*x 0 + (873097799/2000000000 : ℝ)*x 1 + (4365488977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (99827317/250000000 : ℝ)^4665 ≤ (30844737474603/100000000000000 : ℝ)^3641 := by
    have hnat : (99827317 : ℕ)^4665*100000000000000^3641 ≤ 30844737474603^3641*250000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99827317 250000000 30844737474603 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (873097799/2000000000 : ℝ)^4665 ≤ (34577631350509/100000000000000 : ℝ)^3641 := by
    have hnat : (873097799 : ℕ)^4665*100000000000000^3641 ≤ 34577631350509^3641*2000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873097799 2000000000 34577631350509 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4365488977/10000000000 : ℝ)^4665 ≤ (216110194799/625000000000 : ℝ)^3641 := by
    have hnat : (4365488977 : ℕ)^4665*625000000000^3641 ≤ 216110194799^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365488977 10000000000 216110194799 625000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(99827317/250000000 : ℝ), (873097799/2000000000 : ℝ), (4365488977/10000000000 : ℝ)] ![(30844737474603/100000000000000 : ℝ), (34577631350509/100000000000000 : ℝ), (216110194799/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(99827317/250000000 : ℝ)|^4665 ≤ (30844737474603/100000000000000 : ℝ)^3641
        have hw : |(99827317/250000000 : ℝ)|=(99827317/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(873097799/2000000000 : ℝ)|^4665 ≤ (34577631350509/100000000000000 : ℝ)^3641
        have hw : |(873097799/2000000000 : ℝ)|=(873097799/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4365488977/10000000000 : ℝ)|^4665 ≤ (216110194799/625000000000 : ℝ)^3641
        have hw : |(4365488977/10000000000 : ℝ)|=(4365488977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1584_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169154589/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5583/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31927/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58969/100000 : ℝ) ∧ (81059/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (21613/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5583/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5583/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5583/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5583/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5583/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5583/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5583/50000 : ℝ) ^ (4663/1024 : ℝ) ≤ (461743716915409/10000000000000000000 : ℝ) := by
    have hpowers : (5583/50000 : ℝ)^4663 ≤ (461743716915409/10000000000000000000 : ℝ)^1024 := by
      have hnat : (5583 : ℕ)^4663*10000000000000000000^1024 ≤ 461743716915409^1024*50000^4663 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5583 50000 461743716915409 10000000000000000000 4663 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5583/50000 : ℝ)) (X := (461743716915409/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15483/100000 : ℝ) ^ (4663/1024 : ℝ) ≤ (20456643215863907/100000000000000000000 : ℝ) := by
    have hpowers : (15483/100000 : ℝ)^4663 ≤ (20456643215863907/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15483 : ℕ)^4663*100000000000000000000^1024 ≤ 20456643215863907^1024*100000^4663 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15483 100000 20456643215863907 100000000000000000000 4663 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15483/100000 : ℝ)) (X := (20456643215863907/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000461743716915409/5000000000000000000 : ℝ) ≤ (10000202791562967/10000000000000000 : ℝ) ^ (4663/1024 : ℝ) := by
    have hpowers : (5000461743716915409/5000000000000000000 : ℝ)^1024 ≤ (10000202791562967/10000000000000000 : ℝ)^4663 := by
      have hnat : (5000461743716915409 : ℕ)^1024*10000000000000000^4663 ≤ 10000202791562967^4663*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000461743716915409 5000000000000000000 10000202791562967 10000000000000000 1024 4663 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000202791562967/10000000000000000 : ℝ)) (X := (5000461743716915409/5000000000000000000 : ℝ)) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100025074080385017997/100000000000000000000 : ℝ) ≤ (1000055057573643/1000000000000000 : ℝ) ^ (4663/1024 : ℝ) := by
    have hpowers : (100025074080385017997/100000000000000000000 : ℝ)^1024 ≤ (1000055057573643/1000000000000000 : ℝ)^4663 := by
      have hnat : (100025074080385017997 : ℕ)^1024*1000000000000000^4663 ≤ 1000055057573643^4663*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100025074080385017997 100000000000000000000 1000055057573643 1000000000000000 1024 4663 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000055057573643/1000000000000000 : ℝ)) (X := (100025074080385017997/100000000000000000000 : ℝ)) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50020456643215863907/50000000000000000000 : ℝ) ≤ (10000898359909893/10000000000000000 : ℝ) ^ (4663/1024 : ℝ) := by
    have hpowers : (50020456643215863907/50000000000000000000 : ℝ)^1024 ≤ (10000898359909893/10000000000000000 : ℝ)^4663 := by
      have hnat : (50020456643215863907 : ℕ)^1024*10000000000000000^4663 ≤ 10000898359909893^4663*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020456643215863907 50000000000000000000 10000898359909893 10000000000000000 1024 4663 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000898359909893/10000000000000000 : ℝ)) (X := (50020456643215863907/50000000000000000000 : ℝ)) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(461743716915409/10000000000000000000 : ℝ) ≤ ((14387702911671850941/14390000000000000000 : ℝ)+2*(115928057821/143900000000000 : ℝ)*(5583/50000 : ℝ))^(4663/1024 : ℝ) := by
    rw [show (14387702911671850941/14390000000000000000 : ℝ)+2*(115928057821/143900000000000 : ℝ)*(5583/50000 : ℝ)=(10000202791562967/10000000000000000 : ℝ) by norm_num, show 1+2*(461743716915409/10000000000000000000 : ℝ)=(5000461743716915409/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20456643215863907/100000000000000000000 : ℝ)+(461743716915409/10000000000000000000 : ℝ) ≤ ((14387702911671850941/14390000000000000000 : ℝ)+(115928057821/143900000000000 : ℝ)*((15483/100000 : ℝ)+(5583/50000 : ℝ)))^(4663/1024 : ℝ) := by
    rw [show (14387702911671850941/14390000000000000000 : ℝ)+(115928057821/143900000000000 : ℝ)*((15483/100000 : ℝ)+(5583/50000 : ℝ))=(1000055057573643/1000000000000000 : ℝ) by norm_num, show 1+(20456643215863907/100000000000000000000 : ℝ)+(461743716915409/10000000000000000000 : ℝ)=(100025074080385017997/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20456643215863907/100000000000000000000 : ℝ) ≤ ((14387702911671850941/14390000000000000000 : ℝ)+2*(115928057821/143900000000000 : ℝ)*(15483/100000 : ℝ))^(4663/1024 : ℝ) := by
    rw [show (14387702911671850941/14390000000000000000 : ℝ)+2*(115928057821/143900000000000 : ℝ)*(15483/100000 : ℝ)=(10000898359909893/10000000000000000 : ℝ) by norm_num, show 1+2*(20456643215863907/100000000000000000000 : ℝ)=(50020456643215863907/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14387702911671850941/14390000000000000000 : ℝ)*(X 1 0+X 2 0)+(115928057821/143900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4663/1024 : ℝ)) (lo := (5583/50000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (14387702911671850941/14390000000000000000 : ℝ)) (alpha := (115928057821/143900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14387702911671850941/14390000000000000000 : ℝ)*(X 0 1+X 2 1)+(115928057821/143900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4663/1024 : ℝ)) (lo := (5583/50000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (14387702911671850941/14390000000000000000 : ℝ)) (alpha := (115928057821/143900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14387702911671850941/14390000000000000000 : ℝ)*(X 0 2+X 1 2)+(115928057821/143900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4663/1024 : ℝ)) (lo := (5583/50000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (14387702911671850941/14390000000000000000 : ℝ)) (alpha := (115928057821/143900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1565080759/10000000000 : ℝ)*X 0 0+(5395093841/10000000000 : ℝ)*X 0 1+(2697547189/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1317781899/2500000000 : ℝ)*X 1 0+(-1737481241/10000000000 : ℝ)*X 1 1+(1348773571/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1317781873/2500000000 : ℝ)*X 2 0+(5395094343/10000000000 : ℝ)*X 2 1+(-1737481301/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((277347637/625000000 : ℝ)*X 0 0+(1035962447/2500000000 : ℝ)*X 0 1+(828769963/2000000000 : ℝ)*X 0 2+(277347637/625000000 : ℝ)*X 1 0+(1035962447/2500000000 : ℝ)*X 1 1+(828769963/2000000000 : ℝ)*X 1 2+(277347637/625000000 : ℝ)*X 2 0+(1035962447/2500000000 : ℝ)*X 2 1+(828769963/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-123351899/625000000 : ℝ)*X 0 0+(5245278211/10000000000 : ℝ)*X 0 1+(5245278681/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5374869273/10000000000 : ℝ)*X 1 0+(-1800258991/10000000000 : ℝ)*X 1 1+(5245278761/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5374869463/10000000000 : ℝ)*X 2 0+(5245278583/10000000000 : ℝ)*X 2 1+(-1800258973/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1008612243/2500000000 : ℝ)*X 0 0+(869056061/2000000000 : ℝ)*X 0 1+(4345280623/10000000000 : ℝ)*X 0 2+(1008612243/2500000000 : ℝ)*X 1 0+(869056061/2000000000 : ℝ)*X 1 1+(4345280623/10000000000 : ℝ)*X 1 2+(1008612243/2500000000 : ℝ)*X 2 0+(869056061/2000000000 : ℝ)*X 2 1+(4345280623/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-235871937/1250000000 : ℝ)*X 0 0+(5139585343/10000000000 : ℝ)*X 0 1+(5415317811/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5257120807/10000000000 : ℝ)*X 1 0+(-432194609/2500000000 : ℝ)*X 1 1+(135382937/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2628560151/5000000000 : ℝ)*X 2 0+(2707659129/5000000000 : ℝ)*X 2 1+(-345755611/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4490835949/10000000000 : ℝ)*X 0 0+(2058311857/5000000000 : ℝ)*X 0 1+(4116624359/10000000000 : ℝ)*X 0 2+(4490835949/10000000000 : ℝ)*X 1 0+(2058311857/5000000000 : ℝ)*X 1 1+(4116624359/10000000000 : ℝ)*X 1 2+(4490835949/10000000000 : ℝ)*X 2 0+(2058311857/5000000000 : ℝ)*X 2 1+(4116624359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-825667309/5000000000 : ℝ)*X 0 0+(5497605483/10000000000 : ℝ)*X 0 1+(5230229851/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5385291871/10000000000 : ℝ)*X 1 0+(-903198317/5000000000 : ℝ)*X 1 1+(1307557459/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2692645921/5000000000 : ℝ)*X 2 0+(2615114927/5000000000 : ℝ)*X 2 1+(-36127933/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((99827317/250000000 : ℝ)*X 0 0+(873097799/2000000000 : ℝ)*X 0 1+(4365488977/10000000000 : ℝ)*X 0 2+(99827317/250000000 : ℝ)*X 1 0+(873097799/2000000000 : ℝ)*X 1 1+(4365488977/10000000000 : ℝ)*X 1 2+(99827317/250000000 : ℝ)*X 2 0+(873097799/2000000000 : ℝ)*X 2 1+(4365488977/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31927/50000 : ℝ) ≤ (-4594112734968100512901133080293/7195000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (927813/100000000000000 : ℝ)*(lower2) + (13269/250000000000 : ℝ)*(lower3) + (40682059/50000000000000 : ℝ)*(upper5) + (46555993295891/2000000000000 : ℝ)*(major0) + (46555993295891/2000000000000 : ℝ)*(major1) + (46555993295891/2000000000000 : ℝ)*(major2) + (693369359/20000000000000 : ℝ)*(sp2) + (1650423703/100000000000000 : ℝ)*(sp3) + (412592748781799/12500000000000 : ℝ)*(sp4) + (132028836665413/4000000000000 : ℝ)*(sp5) + (82518555586537/2500000000000 : ℝ)*(sp6) + (1376135809727939/100000000000000 : ℝ)*(sp7) + (1850026941/50000000000000 : ℝ)*(sp12) + (495473459/2000000000000 : ℝ)*(sp13) + (688068730075821/50000000000000 : ℝ)*(f.failure) + (132029827612331/4000000000000 : ℝ)*(f.sum) + (91950607199/143900000000000000000000000 : ℝ)*base65 + (366216404074823431/28780000000000000000000000000000 : ℝ)*base67 + (102479865708396569/28780000000000000000000000000000 : ℝ)*base70 + (44531701748863431/28780000000000000000000000000000 : ℝ)*base71 + (3354857778567/719500000000000000000000000 : ℝ)*base73 + (8843476950623431/28780000000000000000000000000000 : ℝ)*base75 + (120829922148963431/28780000000000000000000000000000 : ℝ)*base77 + (160773948349363431/28780000000000000000000000000000 : ℝ)*base79 + (1661079288363/1439000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (59907431/5000000000000000000000 : ℝ)*base90 + (59907431/5000000000000000000000 : ℝ)*base92 + (59907431/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58969/100000 : ℝ) ≤ (4243031783352707253000884337/7195000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6951363/50000000000000 : ℝ)*(lower0) + (7547611/20000000000000 : ℝ)*(upper2) + (89567/10000000000000 : ℝ)*(upper3) + (150562289359249/6250000000000 : ℝ)*(major0) + (150562289359249/6250000000000 : ℝ)*(major1) + (150562289359249/6250000000000 : ℝ)*(major2) + (421773709001963/12500000000000 : ℝ)*(sp0) + (52721736373291/1562500000000 : ℝ)*(sp1) + (1687095691501/50000000000 : ℝ)*(sp2) + (712068937467927/50000000000000 : ℝ)*(sp3) + (1430477949/25000000000000 : ℝ)*(sp5) + (5466800419/100000000000000 : ℝ)*(sp6) + (48727189/4000000000000 : ℝ)*(sp7) + (1435557343/20000000000000 : ℝ)*(sp12) + (712069546557789/50000000000000 : ℝ)*(f.failure) + (168709842490121/5000000000000 : ℝ)*(f.sum) + (21006890358113/3597500000000000000000000000 : ℝ)*base66 + (181586870410978309/89937500000000000000000000000000 : ℝ)*base67 + (90747767119478309/89937500000000000000000000000000 : ℝ)*base69 + (467435981524396691/89937500000000000000000000000000 : ℝ)*base72 + (20225218476749/7195000000000000000000000000 : ℝ)*base73 + (350972744905834191/89937500000000000000000000000000 : ℝ)*base76 + (244119800625334191/89937500000000000000000000000000 : ℝ)*base78 + (453236355720228309/89937500000000000000000000000000 : ℝ)*base79 + (9355805741373/3597500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (36956279/5000000000000000000000 : ℝ)*base90 + (36956279/5000000000000000000000 : ℝ)*base92 + (36956279/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (81059/100000 : ℝ) ≤ (145808830840436188858460821194279/179875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18830047/25000000000000 : ℝ)*(upper0) + (361173/100000000000000 : ℝ)*(upper2) + (48171889/100000000000000 : ℝ)*(lower3) + (1296729949066527/50000000000000 : ℝ)*(major0) + (1296729949066527/50000000000000 : ℝ)*(major1) + (1296729949066527/50000000000000 : ℝ)*(major2) + (111939861/25000000000000 : ℝ)*(sp0) + (130495617757/100000000000000 : ℝ)*(sp2) + (4431383007/10000000000000 : ℝ)*(sp3) + (453338238736207/12500000000000 : ℝ)*(sp8) + (362671019186363/10000000000000 : ℝ)*(sp9) + (226661231015367/6250000000000 : ℝ)*(sp10) + (766572445532627/50000000000000 : ℝ)*(sp11) + (383421453/10000000000000 : ℝ)*(sp12) + (383297301223831/25000000000000 : ℝ)*(f.failure) + (362671019186363/10000000000000 : ℝ)*(f.sum) + (8953340598851/1798750000000000000000000000 : ℝ)*base65 + (1028261001502251907/719500000000000000000000000000000 : ℝ)*base67 + (288452919519748093/719500000000000000000000000000000 : ℝ)*base70 + (85819625331251907/719500000000000000000000000000000 : ℝ)*base71 + (299245337657/3597500000000000000000000000 : ℝ)*base73 + (3187416668901251907/719500000000000000000000000000000 : ℝ)*base75 + (7322968382860251907/719500000000000000000000000000000 : ℝ)*base77 + (4370615347114751907/719500000000000000000000000000000 : ℝ)*base79 + (19390533009371/7195000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (20189541/2500000000000000000000 : ℝ)*base90 + (20189541/2500000000000000000000 : ℝ)*base92 + (20189541/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-21613/25000 : ℝ) ≤ (-77750304535663840162835137523229/89937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2117461/100000000000000 : ℝ)*(lower0) + (6142733/100000000000000 : ℝ)*(upper1) + (25983/5000000000000 : ℝ)*(upper3) + (1085859/10000000000000 : ℝ)*(lower4) + (329285106387877/12500000000000 : ℝ)*(major0) + (329285106387877/12500000000000 : ℝ)*(major1) + (329285106387877/12500000000000 : ℝ)*(major2) + (8629313/100000000000000 : ℝ)*(sp4) + (5960899/50000000000000 : ℝ)*(sp6) + (583163491/20000000000000 : ℝ)*(sp7) + (1870028286824413/50000000000000 : ℝ)*(sp12) + (187002829113907/5000000000000 : ℝ)*(sp13) + (1870028285178171/50000000000000 : ℝ)*(sp14) + (1557318624600829/100000000000000 : ℝ)*(sp15) + (1557321540418283/100000000000000 : ℝ)*(f.failure) + (187002829113907/5000000000000 : ℝ)*(f.sum) + (863489171829/449687500000000000000000000 : ℝ)*base66 + (513919276125982743/179875000000000000000000000000000 : ℝ)*base68 + (3476228989699767257/179875000000000000000000000000000 : ℝ)*base69 + (735685787515142257/179875000000000000000000000000000 : ℝ)*base71 + (23164247988257/3597500000000000000000000000 : ℝ)*base74 + (1098298760285107743/179875000000000000000000000000000 : ℝ)*base76 + (274639080062607743/179875000000000000000000000000000 : ℝ)*base78 + (1679144903518357743/179875000000000000000000000000000 : ℝ)*base80 + (9452527701361/1798750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (51049313/10000000000000000000000 : ℝ)*base90 + (51049313/10000000000000000000000 : ℝ)*base92 + (51049313/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1584_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169154589/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5583/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31927/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58969/100000 : ℝ) else (81059/100000 : ℝ) ≤ X j i ∧ X j i ≤ (21613/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1584_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1584_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169154589/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5583/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31927/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58969/100000 : ℝ) else (81059/100000 : ℝ) ≤ X j i ∧ X j i ≤ (21613/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1584_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1584_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169154589/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5583/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31927/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58969/100000 : ℝ) else (81059/100000 : ℝ) ≤ X j i ∧ X j i ≤ (21613/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1584_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

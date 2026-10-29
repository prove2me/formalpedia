-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c305063_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:32:48.085279+00:00
-- url     : https://prove2.me/submissions/08f8ea16-8506-4036-bb51-fe4a0871d643

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_ordered_majorant
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
theorem raw_linear_data {p k A : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (h : RawFrame p k A X) :
    RawLinearData k A X (fun j => lpNorm p (X j))
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

theorem raw_linear_data_bounds {k A T : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N P : Fin 3 → ℝ}
    (h : RawLinearData k A X N P T) (hA : A ≤ 3) :
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



theorem abs_signValue (b : Bool) : |signValue b|=1 := by
  cases b <;> norm_num [signValue]

theorem abs_signedPair (X : Fin 3 → Fin 3 → ℝ) (signs : Fin 3 → Fin 3 → Bool) (i h : Fin 3) :
    |signedPair X signs i h|=|pair X i h| := by
  simp [signedPair,abs_mul,abs_signValue]

theorem chart_majorant {p k A d a rho alpha beta : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hcorner1 : 1+rho^a ≤ (1+alpha*rho)^a)
    (hcorner2 : 1+2*rho^a ≤ (1+(alpha+beta)*rho)^a)
    (X : Fin 3 → Fin 3 → ℝ) (orders : Fin 3 → Fin 3 → Fin 3)
    (signs : Fin 3 → Fin 3 → Bool) (hX : OrderedChart p k A d X orders signs)
    (i : Fin 3)
    (hratio : signedPair X signs i (orders i 1) ≤ rho*signedPair X signs i (orders i 0)) :
    lpNorm p (pair X i) ≤ signedPair X signs i (orders i 0)+
      alpha*signedPair X signs i (orders i 1)+beta*signedPair X signs i (orders i 2) := by
  obtain ⟨h2,h21,h10⟩ := hX.ordered i
  have h1 : 0 ≤ signedPair X signs i (orders i 1) := h2.trans h21
  have h0 : 0 ≤ signedPair X signs i (orders i 0) := h1.trans h10
  have hh := ordered_majorant (M := signedPair X signs i (orders i 0))
    (u := signedPair X signs i (orders i 1)) (v := signedPair X signs i (orders i 2)) hp ha hap hrho hrho1 halpha hbeta hcorner1 hcorner2 h0
    (by simpa only [abs_of_nonneg h1,abs_of_nonneg h2] using h21)
    (by simpa only [abs_of_nonneg h1] using hratio)
  have he := HlawkaSchatten.DiagonalRealBundle.lpNorm_eq3 p (pair X i)
    (i := orders i 0) (j := orders i 1) (k := orders i 2)
    ((hX.permutation i).1.ne (by decide)) ((hX.permutation i).1.ne (by decide))
    ((hX.permutation i).1.ne (by decide))
  rw [he]
  calc
    _ ≤ signedPair X signs i (orders i 0)+alpha*|signedPair X signs i (orders i 1)|+
        beta*|signedPair X signs i (orders i 2)| := by
      simpa only [abs_signedPair] using hh
    _ = _ := by rw [abs_of_nonneg h1,abs_of_nonneg h2]

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
theorem collision_support_c305063_s2_s2_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-366932989/10000000000 : ℝ)*x 0 + (1419549359/2500000000 : ℝ)*x 1 + (6003501141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (366932989/10000000000 : ℝ)^67 ≤ (1300951289273/100000000000000 : ℝ)^51 := by
    have hnat : (366932989 : ℕ)^67*100000000000000^51 ≤ 1300951289273^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366932989 10000000000 1300951289273 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1419549359/2500000000 : ℝ)^67 ≤ (47544474820849/100000000000000 : ℝ)^51 := by
    have hnat : (1419549359 : ℕ)^67*100000000000000^51 ≤ 47544474820849^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1419549359 2500000000 47544474820849 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6003501141/10000000000 : ℝ)^67 ≤ (10230914773997/20000000000000 : ℝ)^51 := by
    have hnat : (6003501141 : ℕ)^67*20000000000000^51 ≤ 10230914773997^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6003501141 10000000000 10230914773997 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-366932989/10000000000 : ℝ), (1419549359/2500000000 : ℝ), (6003501141/10000000000 : ℝ)] ![(1300951289273/100000000000000 : ℝ), (47544474820849/100000000000000 : ℝ), (10230914773997/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-366932989/10000000000 : ℝ)|^67 ≤ (1300951289273/100000000000000 : ℝ)^51
        have hw : |(-366932989/10000000000 : ℝ)|=(366932989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1419549359/2500000000 : ℝ)|^67 ≤ (47544474820849/100000000000000 : ℝ)^51
        have hw : |(1419549359/2500000000 : ℝ)|=(1419549359/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6003501141/10000000000 : ℝ)|^67 ≤ (10230914773997/20000000000000 : ℝ)^51
        have hw : |(6003501141/10000000000 : ℝ)|=(6003501141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s2_s2_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2872574461/5000000000 : ℝ)*x 0 + (119404359/200000000 : ℝ)*x 1 + (-57089337/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2872574461/5000000000 : ℝ)^67 ≤ (9656460442573/20000000000000 : ℝ)^51 := by
    have hnat : (2872574461 : ℕ)^67*20000000000000^51 ≤ 9656460442573^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2872574461 5000000000 9656460442573 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (119404359/200000000 : ℝ)^67 ≤ (1586947716671/3125000000000 : ℝ)^51 := by
    have hnat : (119404359 : ℕ)^67*3125000000000^51 ≤ 1586947716671^51*200000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119404359 200000000 1586947716671 3125000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (57089337/2000000000 : ℝ)^67 ≤ (935370843687/100000000000000 : ℝ)^51 := by
    have hnat : (57089337 : ℕ)^67*100000000000000^51 ≤ 935370843687^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57089337 2000000000 935370843687 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2872574461/5000000000 : ℝ), (119404359/200000000 : ℝ), (-57089337/2000000000 : ℝ)] ![(9656460442573/20000000000000 : ℝ), (1586947716671/3125000000000 : ℝ), (935370843687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2872574461/5000000000 : ℝ)|^67 ≤ (9656460442573/20000000000000 : ℝ)^51
        have hw : |(2872574461/5000000000 : ℝ)|=(2872574461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(119404359/200000000 : ℝ)|^67 ≤ (1586947716671/3125000000000 : ℝ)^51
        have hw : |(119404359/200000000 : ℝ)|=(119404359/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-57089337/2000000000 : ℝ)|^67 ≤ (935370843687/100000000000000 : ℝ)^51
        have hw : |(-57089337/2000000000 : ℝ)|=(57089337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s2_s2_6 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4851990573/10000000000 : ℝ)*x 0 + (2190103963/5000000000 : ℝ)*x 1 + (3745185481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4851990573/10000000000 : ℝ)^67 ≤ (9667741708641/25000000000000 : ℝ)^51 := by
    have hnat : (4851990573 : ℕ)^67*25000000000000^51 ≤ 9667741708641^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4851990573 10000000000 9667741708641 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2190103963/5000000000 : ℝ)^67 ≤ (8452058470137/25000000000000 : ℝ)^51 := by
    have hnat : (2190103963 : ℕ)^67*25000000000000^51 ≤ 8452058470137^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190103963 5000000000 8452058470137 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3745185481/10000000000 : ℝ)^67 ≤ (27520799275993/100000000000000 : ℝ)^51 := by
    have hnat : (3745185481 : ℕ)^67*100000000000000^51 ≤ 27520799275993^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3745185481 10000000000 27520799275993 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4851990573/10000000000 : ℝ), (2190103963/5000000000 : ℝ), (3745185481/10000000000 : ℝ)] ![(9667741708641/25000000000000 : ℝ), (8452058470137/25000000000000 : ℝ), (27520799275993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4851990573/10000000000 : ℝ)|^67 ≤ (9667741708641/25000000000000 : ℝ)^51
        have hw : |(4851990573/10000000000 : ℝ)|=(4851990573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2190103963/5000000000 : ℝ)|^67 ≤ (8452058470137/25000000000000 : ℝ)^51
        have hw : |(2190103963/5000000000 : ℝ)|=(2190103963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3745185481/10000000000 : ℝ)|^67 ≤ (27520799275993/100000000000000 : ℝ)^51
        have hw : |(3745185481/10000000000 : ℝ)|=(3745185481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s2_s2_7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-787379867/10000000000 : ℝ)*x 0 + (293151619/1250000000 : ℝ)*x 1 + (8563872797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (787379867/10000000000 : ℝ)^67 ≤ (1773614335857/50000000000000 : ℝ)^51 := by
    have hnat : (787379867 : ℕ)^67*50000000000000^51 ≤ 1773614335857^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      787379867 10000000000 1773614335857 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (293151619/1250000000 : ℝ)^67 ≤ (14879639601701/100000000000000 : ℝ)^51 := by
    have hnat : (293151619 : ℕ)^67*100000000000000^51 ≤ 14879639601701^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      293151619 1250000000 14879639601701 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8563872797/10000000000 : ℝ)^67 ≤ (20393282929997/25000000000000 : ℝ)^51 := by
    have hnat : (8563872797 : ℕ)^67*25000000000000^51 ≤ 20393282929997^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8563872797 10000000000 20393282929997 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-787379867/10000000000 : ℝ), (293151619/1250000000 : ℝ), (8563872797/10000000000 : ℝ)] ![(1773614335857/50000000000000 : ℝ), (14879639601701/100000000000000 : ℝ), (20393282929997/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-787379867/10000000000 : ℝ)|^67 ≤ (1773614335857/50000000000000 : ℝ)^51
        have hw : |(-787379867/10000000000 : ℝ)|=(787379867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(293151619/1250000000 : ℝ)|^67 ≤ (14879639601701/100000000000000 : ℝ)^51
        have hw : |(293151619/1250000000 : ℝ)|=(293151619/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8563872797/10000000000 : ℝ)|^67 ≤ (20393282929997/25000000000000 : ℝ)^51
        have hw : |(8563872797/10000000000 : ℝ)|=(8563872797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s2_s2_8 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2715168183/10000000000 : ℝ)*x 0 + (-31129231/2500000000 : ℝ)*x 1 + (2142473267/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2715168183/10000000000 : ℝ)^67 ≤ (18037001410207/100000000000000 : ℝ)^51 := by
    have hnat : (2715168183 : ℕ)^67*100000000000000^51 ≤ 18037001410207^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715168183 10000000000 18037001410207 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (31129231/2500000000 : ℝ)^67 ≤ (157261704613/50000000000000 : ℝ)^51 := by
    have hnat : (31129231 : ℕ)^67*50000000000000^51 ≤ 157261704613^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31129231 2500000000 157261704613 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2142473267/2500000000 : ℝ)^67 ≤ (10206059395669/12500000000000 : ℝ)^51 := by
    have hnat : (2142473267 : ℕ)^67*12500000000000^51 ≤ 10206059395669^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142473267 2500000000 10206059395669 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2715168183/10000000000 : ℝ), (-31129231/2500000000 : ℝ), (2142473267/2500000000 : ℝ)] ![(18037001410207/100000000000000 : ℝ), (157261704613/50000000000000 : ℝ), (10206059395669/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2715168183/10000000000 : ℝ)|^67 ≤ (18037001410207/100000000000000 : ℝ)^51
        have hw : |(2715168183/10000000000 : ℝ)|=(2715168183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-31129231/2500000000 : ℝ)|^67 ≤ (157261704613/50000000000000 : ℝ)^51
        have hw : |(-31129231/2500000000 : ℝ)|=(31129231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2142473267/2500000000 : ℝ)|^67 ≤ (10206059395669/12500000000000 : ℝ)^51
        have hw : |(2142473267/2500000000 : ℝ)|=(2142473267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s2_s2_9 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1403693231/5000000000 : ℝ)*x 0 + (213146683/250000000 : ℝ)*x 1 + (-6701011/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1403693231/5000000000 : ℝ)^67 ≤ (4711514669213/25000000000000 : ℝ)^51 := by
    have hnat : (1403693231 : ℕ)^67*25000000000000^51 ≤ 4711514669213^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1403693231 5000000000 4711514669213 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (213146683/250000000 : ℝ)^67 ≤ (81097878574413/100000000000000 : ℝ)^51 := by
    have hnat : (213146683 : ℕ)^67*100000000000000^51 ≤ 81097878574413^51*250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213146683 250000000 81097878574413 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6701011/2000000000 : ℝ)^67 ≤ (28031372733/50000000000000 : ℝ)^51 := by
    have hnat : (6701011 : ℕ)^67*50000000000000^51 ≤ 28031372733^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6701011 2000000000 28031372733 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1403693231/5000000000 : ℝ), (213146683/250000000 : ℝ), (-6701011/2000000000 : ℝ)] ![(4711514669213/25000000000000 : ℝ), (81097878574413/100000000000000 : ℝ), (28031372733/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1403693231/5000000000 : ℝ)|^67 ≤ (4711514669213/25000000000000 : ℝ)^51
        have hw : |(1403693231/5000000000 : ℝ)|=(1403693231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(213146683/250000000 : ℝ)|^67 ≤ (81097878574413/100000000000000 : ℝ)^51
        have hw : |(213146683/250000000 : ℝ)|=(213146683/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6701011/2000000000 : ℝ)|^67 ≤ (28031372733/50000000000000 : ℝ)^51
        have hw : |(-6701011/2000000000 : ℝ)|=(6701011/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s2_s2_13 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1524072897/5000000000 : ℝ)*x 0 + (3740977937/5000000000 : ℝ)*x 1 + (364707983/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1524072897/5000000000 : ℝ)^67 ≤ (10498677572843/50000000000000 : ℝ)^51 := by
    have hnat : (1524072897 : ℕ)^67*50000000000000^51 ≤ 10498677572843^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1524072897 5000000000 10498677572843 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3740977937/5000000000 : ℝ)^67 ≤ (34155487290939/50000000000000 : ℝ)^51 := by
    have hnat : (3740977937 : ℕ)^67*50000000000000^51 ≤ 34155487290939^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3740977937 5000000000 34155487290939 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (364707983/2000000000 : ℝ)^67 ≤ (5345835125561/50000000000000 : ℝ)^51 := by
    have hnat : (364707983 : ℕ)^67*50000000000000^51 ≤ 5345835125561^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      364707983 2000000000 5345835125561 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1524072897/5000000000 : ℝ), (3740977937/5000000000 : ℝ), (364707983/2000000000 : ℝ)] ![(10498677572843/50000000000000 : ℝ), (34155487290939/50000000000000 : ℝ), (5345835125561/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1524072897/5000000000 : ℝ)|^67 ≤ (10498677572843/50000000000000 : ℝ)^51
        have hw : |(1524072897/5000000000 : ℝ)|=(1524072897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3740977937/5000000000 : ℝ)|^67 ≤ (34155487290939/50000000000000 : ℝ)^51
        have hw : |(3740977937/5000000000 : ℝ)|=(3740977937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(364707983/2000000000 : ℝ)|^67 ≤ (5345835125561/50000000000000 : ℝ)^51
        have hw : |(364707983/2000000000 : ℝ)|=(364707983/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s2_s2_14 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-45024771/5000000000 : ℝ)*x 0 + (659013183/2500000000 : ℝ)*x 1 + (863344231/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (45024771/5000000000 : ℝ)^67 ≤ (51367712411/25000000000000 : ℝ)^51 := by
    have hnat : (45024771 : ℕ)^67*25000000000000^51 ≤ 51367712411^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45024771 5000000000 51367712411 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (659013183/2500000000 : ℝ)^67 ≤ (17349726496503/100000000000000 : ℝ)^51 := by
    have hnat : (659013183 : ℕ)^67*100000000000000^51 ≤ 17349726496503^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659013183 2500000000 17349726496503 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (863344231/1000000000 : ℝ)^67 ≤ (41222401321709/50000000000000 : ℝ)^51 := by
    have hnat : (863344231 : ℕ)^67*50000000000000^51 ≤ 41222401321709^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863344231 1000000000 41222401321709 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-45024771/5000000000 : ℝ), (659013183/2500000000 : ℝ), (863344231/1000000000 : ℝ)] ![(51367712411/25000000000000 : ℝ), (17349726496503/100000000000000 : ℝ), (41222401321709/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-45024771/5000000000 : ℝ)|^67 ≤ (51367712411/25000000000000 : ℝ)^51
        have hw : |(-45024771/5000000000 : ℝ)|=(45024771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(659013183/2500000000 : ℝ)|^67 ≤ (17349726496503/100000000000000 : ℝ)^51
        have hw : |(659013183/2500000000 : ℝ)|=(659013183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(863344231/1000000000 : ℝ)|^67 ≤ (41222401321709/50000000000000 : ℝ)^51
        have hw : |(863344231/1000000000 : ℝ)|=(863344231/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s2_s2_15 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2254123101/10000000000 : ℝ)*x 0 + (-94309807/1250000000 : ℝ)*x 1 + (8639527429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2254123101/10000000000 : ℝ)^67 ≤ (220704020977/1562500000000 : ℝ)^51 := by
    have hnat : (2254123101 : ℕ)^67*1562500000000^51 ≤ 220704020977^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254123101 10000000000 220704020977 1562500000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (94309807/1250000000 : ℝ)^67 ≤ (167689570777/5000000000000 : ℝ)^51 := by
    have hnat : (94309807 : ℕ)^67*5000000000000^51 ≤ 167689570777^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94309807 1250000000 167689570777 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8639527429/10000000000 : ℝ)^67 ≤ (82521151229671/100000000000000 : ℝ)^51 := by
    have hnat : (8639527429 : ℕ)^67*100000000000000^51 ≤ 82521151229671^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8639527429 10000000000 82521151229671 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2254123101/10000000000 : ℝ), (-94309807/1250000000 : ℝ), (8639527429/10000000000 : ℝ)] ![(220704020977/1562500000000 : ℝ), (167689570777/5000000000000 : ℝ), (82521151229671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2254123101/10000000000 : ℝ)|^67 ≤ (220704020977/1562500000000 : ℝ)^51
        have hw : |(2254123101/10000000000 : ℝ)|=(2254123101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-94309807/1250000000 : ℝ)|^67 ≤ (167689570777/5000000000000 : ℝ)^51
        have hw : |(-94309807/1250000000 : ℝ)|=(94309807/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8639527429/10000000000 : ℝ)|^67 ≤ (82521151229671/100000000000000 : ℝ)^51
        have hw : |(8639527429/10000000000 : ℝ)|=(8639527429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s2_s2_16 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8355067327/10000000000 : ℝ)*x 0 + (303953919/1000000000 : ℝ)*x 1 + (-56051273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8355067327/10000000000 : ℝ)^67 ≤ (4935642352733/6250000000000 : ℝ)^51 := by
    have hnat : (8355067327 : ℕ)^67*6250000000000^51 ≤ 4935642352733^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8355067327 10000000000 4935642352733 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (303953919/1000000000 : ℝ)^67 ≤ (10459751302939/50000000000000 : ℝ)^51 := by
    have hnat : (303953919 : ℕ)^67*50000000000000^51 ≤ 10459751302939^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      303953919 1000000000 10459751302939 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56051273/10000000000 : ℝ)^67 ≤ (110219733517/100000000000000 : ℝ)^51 := by
    have hnat : (56051273 : ℕ)^67*100000000000000^51 ≤ 110219733517^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56051273 10000000000 110219733517 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8355067327/10000000000 : ℝ), (303953919/1000000000 : ℝ), (-56051273/10000000000 : ℝ)] ![(4935642352733/6250000000000 : ℝ), (10459751302939/50000000000000 : ℝ), (110219733517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8355067327/10000000000 : ℝ)|^67 ≤ (4935642352733/6250000000000 : ℝ)^51
        have hw : |(8355067327/10000000000 : ℝ)|=(8355067327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(303953919/1000000000 : ℝ)|^67 ≤ (10459751302939/50000000000000 : ℝ)^51
        have hw : |(303953919/1000000000 : ℝ)|=(303953919/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-56051273/10000000000 : ℝ)|^67 ≤ (110219733517/100000000000000 : ℝ)^51
        have hw : |(-56051273/10000000000 : ℝ)|=(56051273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s2_s2_20 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3868475181/5000000000 : ℝ)*x 0 + (2709287171/10000000000 : ℝ)*x 1 + (907672279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3868475181/5000000000 : ℝ)^67 ≤ (3569285799167/5000000000000 : ℝ)^51 := by
    have hnat : (3868475181 : ℕ)^67*5000000000000^51 ≤ 3569285799167^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3868475181 5000000000 3569285799167 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2709287171/10000000000 : ℝ)^67 ≤ (719427776319/4000000000000 : ℝ)^51 := by
    have hnat : (2709287171 : ℕ)^67*4000000000000^51 ≤ 719427776319^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709287171 10000000000 719427776319 4000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (907672279/5000000000 : ℝ)^67 ≤ (5314294797933/50000000000000 : ℝ)^51 := by
    have hnat : (907672279 : ℕ)^67*50000000000000^51 ≤ 5314294797933^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      907672279 5000000000 5314294797933 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3868475181/5000000000 : ℝ), (2709287171/10000000000 : ℝ), (907672279/5000000000 : ℝ)] ![(3569285799167/5000000000000 : ℝ), (719427776319/4000000000000 : ℝ), (5314294797933/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3868475181/5000000000 : ℝ)|^67 ≤ (3569285799167/5000000000000 : ℝ)^51
        have hw : |(3868475181/5000000000 : ℝ)|=(3868475181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2709287171/10000000000 : ℝ)|^67 ≤ (719427776319/4000000000000 : ℝ)^51
        have hw : |(2709287171/10000000000 : ℝ)|=(2709287171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(907672279/5000000000 : ℝ)|^67 ≤ (5314294797933/50000000000000 : ℝ)^51
        have hw : |(907672279/5000000000 : ℝ)|=(907672279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s2_s2_21 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-165246333/10000000000 : ℝ)*x 0 + (156214663/200000000 : ℝ)*x 1 + (929598529/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165246333/10000000000 : ℝ)^67 ≤ (91231404659/20000000000000 : ℝ)^51 := by
    have hnat : (165246333 : ℕ)^67*20000000000000^51 ≤ 91231404659^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165246333 10000000000 91231404659 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (156214663/200000000 : ℝ)^67 ≤ (18070346980203/25000000000000 : ℝ)^51 := by
    have hnat : (156214663 : ℕ)^67*25000000000000^51 ≤ 18070346980203^51*200000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156214663 200000000 18070346980203 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (929598529/2500000000 : ℝ)^67 ≤ (3407806880301/12500000000000 : ℝ)^51 := by
    have hnat : (929598529 : ℕ)^67*12500000000000^51 ≤ 3407806880301^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      929598529 2500000000 3407806880301 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-165246333/10000000000 : ℝ), (156214663/200000000 : ℝ), (929598529/2500000000 : ℝ)] ![(91231404659/20000000000000 : ℝ), (18070346980203/25000000000000 : ℝ), (3407806880301/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-165246333/10000000000 : ℝ)|^67 ≤ (91231404659/20000000000000 : ℝ)^51
        have hw : |(-165246333/10000000000 : ℝ)|=(165246333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(156214663/200000000 : ℝ)|^67 ≤ (18070346980203/25000000000000 : ℝ)^51
        have hw : |(156214663/200000000 : ℝ)|=(156214663/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(929598529/2500000000 : ℝ)|^67 ≤ (3407806880301/12500000000000 : ℝ)^51
        have hw : |(929598529/2500000000 : ℝ)|=(929598529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s2_s2_22 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1655425541/2000000000 : ℝ)*x 0 + (-2190389/500000000 : ℝ)*x 1 + (3149174249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1655425541/2000000000 : ℝ)^67 ≤ (78003916835341/100000000000000 : ℝ)^51 := by
    have hnat : (1655425541 : ℕ)^67*100000000000000^51 ≤ 78003916835341^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1655425541 2000000000 78003916835341 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2190389/500000000 : ℝ)^67 ≤ (39867202141/50000000000000 : ℝ)^51 := by
    have hnat : (2190389 : ℕ)^67*50000000000000^51 ≤ 39867202141^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190389 500000000 39867202141 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3149174249/10000000000 : ℝ)^67 ≤ (21916348747457/100000000000000 : ℝ)^51 := by
    have hnat : (3149174249 : ℕ)^67*100000000000000^51 ≤ 21916348747457^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3149174249 10000000000 21916348747457 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1655425541/2000000000 : ℝ), (-2190389/500000000 : ℝ), (3149174249/10000000000 : ℝ)] ![(78003916835341/100000000000000 : ℝ), (39867202141/50000000000000 : ℝ), (21916348747457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1655425541/2000000000 : ℝ)|^67 ≤ (78003916835341/100000000000000 : ℝ)^51
        have hw : |(1655425541/2000000000 : ℝ)|=(1655425541/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2190389/500000000 : ℝ)|^67 ≤ (39867202141/50000000000000 : ℝ)^51
        have hw : |(-2190389/500000000 : ℝ)|=(2190389/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3149174249/10000000000 : ℝ)|^67 ≤ (21916348747457/100000000000000 : ℝ)^51
        have hw : |(3149174249/10000000000 : ℝ)|=(3149174249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s2_s2_23 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (418304991/2000000000 : ℝ)*x 0 + (4396979131/5000000000 : ℝ)*x 1 + (-645749267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (418304991/2000000000 : ℝ)^67 ≤ (3200479110323/25000000000000 : ℝ)^51 := by
    have hnat : (418304991 : ℕ)^67*25000000000000^51 ≤ 3200479110323^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418304991 2000000000 3200479110323 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4396979131/5000000000 : ℝ)^67 ≤ (84464384871777/100000000000000 : ℝ)^51 := by
    have hnat : (4396979131 : ℕ)^67*100000000000000^51 ≤ 84464384871777^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4396979131 5000000000 84464384871777 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (645749267/10000000000 : ℝ)^67 ≤ (2733698676161/100000000000000 : ℝ)^51 := by
    have hnat : (645749267 : ℕ)^67*100000000000000^51 ≤ 2733698676161^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      645749267 10000000000 2733698676161 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(418304991/2000000000 : ℝ), (4396979131/5000000000 : ℝ), (-645749267/10000000000 : ℝ)] ![(3200479110323/25000000000000 : ℝ), (84464384871777/100000000000000 : ℝ), (2733698676161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(418304991/2000000000 : ℝ)|^67 ≤ (3200479110323/25000000000000 : ℝ)^51
        have hw : |(418304991/2000000000 : ℝ)|=(418304991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4396979131/5000000000 : ℝ)|^67 ≤ (84464384871777/100000000000000 : ℝ)^51
        have hw : |(4396979131/5000000000 : ℝ)|=(4396979131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-645749267/10000000000 : ℝ)|^67 ≤ (2733698676161/100000000000000 : ℝ)^51
        have hw : |(-645749267/10000000000 : ℝ)|=(645749267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s2_s2_27 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7864627509/10000000000 : ℝ)*x 0 + (2543435759/10000000000 : ℝ)*x 1 + (359963803/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7864627509/10000000000 : ℝ)^67 ≤ (72937309153221/100000000000000 : ℝ)^51 := by
    have hnat : (7864627509 : ℕ)^67*100000000000000^51 ≤ 72937309153221^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7864627509 10000000000 72937309153221 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2543435759/10000000000 : ℝ)^67 ≤ (8276679109419/50000000000000 : ℝ)^51 := by
    have hnat : (2543435759 : ℕ)^67*50000000000000^51 ≤ 8276679109419^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2543435759 10000000000 8276679109419 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (359963803/2000000000 : ℝ)^67 ≤ (1313666576209/12500000000000 : ℝ)^51 := by
    have hnat : (359963803 : ℕ)^67*12500000000000^51 ≤ 1313666576209^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      359963803 2000000000 1313666576209 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7864627509/10000000000 : ℝ), (2543435759/10000000000 : ℝ), (359963803/2000000000 : ℝ)] ![(72937309153221/100000000000000 : ℝ), (8276679109419/50000000000000 : ℝ), (1313666576209/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7864627509/10000000000 : ℝ)|^67 ≤ (72937309153221/100000000000000 : ℝ)^51
        have hw : |(7864627509/10000000000 : ℝ)|=(7864627509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2543435759/10000000000 : ℝ)|^67 ≤ (8276679109419/50000000000000 : ℝ)^51
        have hw : |(2543435759/10000000000 : ℝ)|=(2543435759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(359963803/2000000000 : ℝ)|^67 ≤ (1313666576209/12500000000000 : ℝ)^51
        have hw : |(359963803/2000000000 : ℝ)|=(359963803/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c305063_s2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((44627/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(44627/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22231/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(22231/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43199/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(43199/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((82347/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(82347/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(82379/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(82379/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79539/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(79539/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76771/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76771/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (93447/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base60 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.2.1]
  have base62 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base63 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base64 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base65 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base66 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base67 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base68 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base69 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base70 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base71 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base72 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base73 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base74 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base75 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base76 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base77 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base78 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base79 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base80 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base81 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base82 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base83 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base84 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base85 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base86 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base87 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base88 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base89 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base90 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base91 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base92 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have base93 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (44627/50000 : ℝ) ^ (133/32 : ℝ) ≤ (12468847866401317687/20000000000000000000 : ℝ) := by
    have hpowers : (44627/50000 : ℝ)^133 ≤ (12468847866401317687/20000000000000000000 : ℝ)^32 := by
      have hnat : (44627 : ℕ)^133*20000000000000000000^32 ≤ 12468847866401317687^32*50000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        44627 50000 12468847866401317687 20000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (44627/50000 : ℝ)) (X := (12468847866401317687/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner0a : (32468847866401317687/20000000000000000000 : ℝ) ≤ (449460387345461/400000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (32468847866401317687/20000000000000000000 : ℝ)^32 ≤ (449460387345461/400000000000000 : ℝ)^133 := by
      have hnat : (32468847866401317687 : ℕ)^32*400000000000000^133 ≤ 449460387345461^133*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32468847866401317687 20000000000000000000 449460387345461 400000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (449460387345461/400000000000000 : ℝ)) (X := (32468847866401317687/20000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner0b : (22468847866401317687/10000000000000000000 : ℝ) ≤ (12150408242228669/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (22468847866401317687/10000000000000000000 : ℝ)^32 ≤ (12150408242228669/10000000000000000 : ℝ)^133 := by
      have hnat : (22468847866401317687 : ℕ)^32*10000000000000000^133 ≤ 12150408242228669^133*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22468847866401317687 10000000000000000000 12150408242228669 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12150408242228669/10000000000000000 : ℝ)) (X := (22468847866401317687/10000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(49460387345461/357016000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(57118659912009/557837500000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (44627/50000 : ℝ)) (alpha := (49460387345461/357016000000000 : ℝ)) (beta := (57118659912009/557837500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (44627/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(49460387345461/357016000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(57118659912009/557837500000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (22231/25000 : ℝ) ^ (133/32 : ℝ) ≤ (61391773165116922961/100000000000000000000 : ℝ) := by
    have hpowers : (22231/25000 : ℝ)^133 ≤ (61391773165116922961/100000000000000000000 : ℝ)^32 := by
      have hnat : (22231 : ℕ)^133*100000000000000000000^32 ≤ 61391773165116922961^32*25000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22231 25000 61391773165116922961 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22231/25000 : ℝ)) (X := (61391773165116922961/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner1a : (161391773165116922961/100000000000000000000 : ℝ) ≤ (2244122558719917/2000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (161391773165116922961/100000000000000000000 : ℝ)^32 ≤ (2244122558719917/2000000000000000 : ℝ)^133 := by
      have hnat : (161391773165116922961 : ℕ)^32*2000000000000000^133 ≤ 2244122558719917^133*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        161391773165116922961 100000000000000000000 2244122558719917 2000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2244122558719917/2000000000000000 : ℝ)) (X := (161391773165116922961/100000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner1b : (111391773165116922961/50000000000000000000 : ℝ) ≤ (6062771556183481/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (111391773165116922961/50000000000000000000 : ℝ)^32 ≤ (6062771556183481/5000000000000000 : ℝ)^133 := by
      have hnat : (111391773165116922961 : ℕ)^32*5000000000000000^133 ≤ 6062771556183481^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        111391773165116922961 50000000000000000000 6062771556183481 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6062771556183481/5000000000000000 : ℝ)) (X := (111391773165116922961/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(244122558719917/1778480000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(904930318767377/8892400000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (22231/25000 : ℝ)) (alpha := (244122558719917/1778480000000000 : ℝ)) (beta := (904930318767377/8892400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (22231/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(244122558719917/1778480000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(904930318767377/8892400000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (43199/50000 : ℝ) ^ (133/32 : ℝ) ≤ (54461984025404649389/100000000000000000000 : ℝ) := by
    have hpowers : (43199/50000 : ℝ)^133 ≤ (54461984025404649389/100000000000000000000 : ℝ)^32 := by
      have hnat : (43199 : ℕ)^133*100000000000000000000^32 ≤ 54461984025404649389^32*50000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        43199 50000 54461984025404649389 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (43199/50000 : ℝ)) (X := (54461984025404649389/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner2a : (154461984025404649389/100000000000000000000 : ℝ) ≤ (173480549484899/156250000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (154461984025404649389/100000000000000000000 : ℝ)^32 ≤ (173480549484899/156250000000000 : ℝ)^133 := by
      have hnat : (154461984025404649389 : ℕ)^32*156250000000000^133 ≤ 173480549484899^133*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        154461984025404649389 100000000000000000000 173480549484899 156250000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (173480549484899/156250000000000 : ℝ)) (X := (154461984025404649389/100000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner2b : (104461984025404649389/50000000000000000000 : ℝ) ≤ (11939596717314433/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (104461984025404649389/50000000000000000000 : ℝ)^32 ≤ (11939596717314433/10000000000000000 : ℝ)^133 := by
      have hnat : (104461984025404649389 : ℕ)^32*10000000000000000^133 ≤ 11939596717314433^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        104461984025404649389 50000000000000000000 11939596717314433 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11939596717314433/10000000000000000 : ℝ)) (X := (104461984025404649389/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(17230549484899/134996875000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(836841550280897/8639800000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (43199/50000 : ℝ)) (alpha := (17230549484899/134996875000000 : ℝ)) (beta := (836841550280897/8639800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (43199/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(17230549484899/134996875000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(836841550280897/8639800000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-366932989/10000000000 : ℝ)*X 0 0+(1419549359/2500000000 : ℝ)*X 0 1+(6003501141/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((2872574461/5000000000 : ℝ)*X 2 0+(119404359/200000000 : ℝ)*X 2 1+(-57089337/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((4851990573/10000000000 : ℝ)*X 0 0+(2190103963/5000000000 : ℝ)*X 0 1+(3745185481/10000000000 : ℝ)*X 0 2+(4851990573/10000000000 : ℝ)*X 1 0+(2190103963/5000000000 : ℝ)*X 1 1+(3745185481/10000000000 : ℝ)*X 1 2+(4851990573/10000000000 : ℝ)*X 2 0+(2190103963/5000000000 : ℝ)*X 2 1+(3745185481/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-787379867/10000000000 : ℝ)*X 0 0+(293151619/1250000000 : ℝ)*X 0 1+(8563872797/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((2715168183/10000000000 : ℝ)*X 1 0+(-31129231/2500000000 : ℝ)*X 1 1+(2142473267/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((1403693231/5000000000 : ℝ)*X 2 0+(213146683/250000000 : ℝ)*X 2 1+(-6701011/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((1524072897/5000000000 : ℝ)*X 0 0+(3740977937/5000000000 : ℝ)*X 0 1+(364707983/2000000000 : ℝ)*X 0 2+(1524072897/5000000000 : ℝ)*X 1 0+(3740977937/5000000000 : ℝ)*X 1 1+(364707983/2000000000 : ℝ)*X 1 2+(1524072897/5000000000 : ℝ)*X 2 0+(3740977937/5000000000 : ℝ)*X 2 1+(364707983/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-45024771/5000000000 : ℝ)*X 0 0+(659013183/2500000000 : ℝ)*X 0 1+(863344231/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((2254123101/10000000000 : ℝ)*X 1 0+(-94309807/1250000000 : ℝ)*X 1 1+(8639527429/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((8355067327/10000000000 : ℝ)*X 2 0+(303953919/1000000000 : ℝ)*X 2 1+(-56051273/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((3868475181/5000000000 : ℝ)*X 0 0+(2709287171/10000000000 : ℝ)*X 0 1+(907672279/5000000000 : ℝ)*X 0 2+(3868475181/5000000000 : ℝ)*X 1 0+(2709287171/10000000000 : ℝ)*X 1 1+(907672279/5000000000 : ℝ)*X 1 2+(3868475181/5000000000 : ℝ)*X 2 0+(2709287171/10000000000 : ℝ)*X 2 1+(907672279/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-165246333/10000000000 : ℝ)*X 0 0+(156214663/200000000 : ℝ)*X 0 1+(929598529/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((1655425541/2000000000 : ℝ)*X 1 0+(-2190389/500000000 : ℝ)*X 1 1+(3149174249/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((418304991/2000000000 : ℝ)*X 2 0+(4396979131/5000000000 : ℝ)*X 2 1+(-645749267/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((7864627509/10000000000 : ℝ)*X 0 0+(2543435759/10000000000 : ℝ)*X 0 1+(359963803/2000000000 : ℝ)*X 0 2+(7864627509/10000000000 : ℝ)*X 1 0+(2543435759/10000000000 : ℝ)*X 1 1+(359963803/2000000000 : ℝ)*X 1 2+(7864627509/10000000000 : ℝ)*X 2 0+(2543435759/10000000000 : ℝ)*X 2 1+(359963803/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((82347/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(82347/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3855956874660828858451876443117/779233644646600000000000000000000000 : ℝ) := by norm_num
    linear_combination (803243630939/1000000000000 : ℝ)*(base7) + (653911/1000000000000 : ℝ)*(base50) + (174389/250000000000 : ℝ)*(base60) + (1656702288963/1000000000000 : ℝ)*(major_s2_0) + (1656702288963/1000000000000 : ℝ)*(major_s2_1) + (1656702288963/1000000000000 : ℝ)*(major_s2_2) + (700763/200000000000 : ℝ)*(sp_s2_0) + (315847/1000000000000 : ℝ)*(sp_s2_6) + (1729637557447/1000000000000 : ℝ)*(sp_s2_7) + (432419030721/250000000000 : ℝ)*(sp_s2_8) + (1729676459211/1000000000000 : ℝ)*(sp_s2_9) + (377313013427/200000000000 : ℝ)*(sp_s2_13) + (35397949/1000000000000 : ℝ)*(sp_s2_14) + (336327/1000000000000 : ℝ)*(sp_s2_15) + (541660876021/500000000000 : ℝ)*(f.failure) + (1729676459211/1000000000000 : ℝ)*(f.sum) + (17431478469307549221/384142787600000000000000000000000 : ℝ)*base63 + (5651266707198909/8639800000000000000000000000 : ℝ)*base64 + (1633991940145011/8892400000000000000000000000 : ℝ)*base67 + (70874393418587/134996875000000000000000000 : ℝ)*base69 + (141812951249287772359/192784177300000000000000000000000 : ℝ)*base70 + (356990652458477/2231350000000000000000000000 : ℝ)*base72 + (448576108373473/1778480000000000000000000000 : ℝ)*base74 + (668877540587941/1785080000000000000000000000 : ℝ)*base76 + (7593652548019710771/36076466800000000000000000000000 : ℝ)*base79 + (657/3125000000000000 : ℝ)*base86 + (657/3125000000000000 : ℝ)*base88 + (657/3125000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(82379/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(82379/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5894721585857246786724498463473/389616822323300000000000000000000000 : ℝ) := by norm_num
    linear_combination (40494721427/50000000000 : ℝ)*(base7) + (31919/50000000000 : ℝ)*(base40) + (1824647/500000000000 : ℝ)*(base53) + (1611384431793/1000000000000 : ℝ)*(major_s2_0) + (1611384431793/1000000000000 : ℝ)*(major_s2_1) + (1611380782499/1000000000000 : ℝ)*(major_s2_2) + (1513609/200000000000 : ℝ)*(sp_s2_6) + (2066721/500000000000 : ℝ)*(sp_s2_7) + (103774023/1000000000000 : ℝ)*(sp_s2_8) + (832259857089/500000000000 : ℝ)*(sp_s2_14) + (416105018399/250000000000 : ℝ)*(sp_s2_15) + (1664527496913/1000000000000 : ℝ)*(sp_s2_16) + (1863244917053/1000000000000 : ℝ)*(sp_s2_20) + (165117919/500000000000 : ℝ)*(sp_s2_27) + (210737658479/200000000000 : ℝ)*(f.failure) + (1664527496913/1000000000000 : ℝ)*(f.sum) + (289208262911914327017/384142787600000000000000000000000 : ℝ)*base62 + (5062797101941297/8639800000000000000000000000 : ℝ)*base64 + (8684634426468359/8892400000000000000000000000 : ℝ)*base66 + (767700835078397/1079975000000000000000000000 : ℝ)*base68 + (4334278929901921929/24098022162500000000000000000000 : ℝ)*base70 + (864064363712447/2231350000000000000000000000 : ℝ)*base72 + (929064123477091/1778480000000000000000000000 : ℝ)*base74 + (34503469850119/357016000000000000000000000 : ℝ)*base76 + (20835862744522872359/36076466800000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (129/156250000000000 : ℝ)*base87 + (129/156250000000000 : ℝ)*base89 + (129/156250000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79539/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(79539/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (12239633024755186263029794371/885492778007500000000000000000000 : ℝ) := by norm_num
    linear_combination (810881743651/1000000000000 : ℝ)*(base7) + (806189/200000000000 : ℝ)*(base27) + (18323669923/200000000000 : ℝ)*(base40) + (11777843/1000000000000 : ℝ)*(base43) + (244471/200000000000 : ℝ)*(base49) + (1558268033597/1000000000000 : ℝ)*(major_s2_0) + (779128127877/500000000000 : ℝ)*(major_s2_1) + (1558268033597/1000000000000 : ℝ)*(major_s2_2) + (775297/1000000000000 : ℝ)*(sp_s2_2) + (99114861/1000000000000 : ℝ)*(sp_s2_9) + (1592401225867/1000000000000 : ℝ)*(sp_s2_21) + (1592413003711/1000000000000 : ℝ)*(sp_s2_22) + (1592301335709/1000000000000 : ℝ)*(sp_s2_23) + (1829833060057/1000000000000 : ℝ)*(sp_s2_27) + (1018955347351/1000000000000 : ℝ)*(f.failure) + (1592413003711/1000000000000 : ℝ)*(f.sum) + (6760350356980094423/17461035800000000000000000000000 : ℝ)*base62 + (6519446152250769/8639800000000000000000000000 : ℝ)*base65 + (212024176106899/404200000000000000000000000 : ℝ)*base67 + (228840397338603/539987500000000000000000000 : ℝ)*base68 + (9256402317761911021/17525834300000000000000000000000 : ℝ)*base70 + (69677905033991/101425000000000000000000000 : ℝ)*base73 + (2116562514797/80840000000000000000000000 : ℝ)*base74 + (63139121653187/162280000000000000000000000 : ℝ)*base77 + (793482119232637591/1639839400000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (49/781250000000000 : ℝ)*base86 + (49/781250000000000 : ℝ)*base88 + (49/781250000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((44627/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(44627/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22231/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(22231/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43199/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(43199/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((82347/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(82347/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(82379/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(82379/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79539/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(79539/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c305063_s2 p hpa hpb X hX hprev1

#print axioms solution

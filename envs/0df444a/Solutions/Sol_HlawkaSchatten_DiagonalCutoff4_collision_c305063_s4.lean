-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c305063_s4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:32:49.57805+00:00
-- url     : https://prove2.me/submissions/fb0500dd-47fb-4389-9c22-e41dbc16d615

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
theorem collision_support_c305063_s4_s4_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-469555079/5000000000 : ℝ)*x 0 + (1122855249/2000000000 : ℝ)*x 1 + (2890845047/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (469555079/5000000000 : ℝ)^67 ≤ (89425530707/2000000000000 : ℝ)^51 := by
    have hnat : (469555079 : ℕ)^67*2000000000000^51 ≤ 89425530707^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469555079 5000000000 89425530707 2000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122855249/2000000000 : ℝ)^67 ≤ (4684258412613/10000000000000 : ℝ)^51 := by
    have hnat : (1122855249 : ℕ)^67*10000000000000^51 ≤ 4684258412613^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122855249 2000000000 4684258412613 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2890845047/5000000000 : ℝ)^67 ≤ (12171534832061/25000000000000 : ℝ)^51 := by
    have hnat : (2890845047 : ℕ)^67*25000000000000^51 ≤ 12171534832061^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2890845047 5000000000 12171534832061 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-469555079/5000000000 : ℝ), (1122855249/2000000000 : ℝ), (2890845047/5000000000 : ℝ)] ![(89425530707/2000000000000 : ℝ), (4684258412613/10000000000000 : ℝ), (12171534832061/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-469555079/5000000000 : ℝ)|^67 ≤ (89425530707/2000000000000 : ℝ)^51
        have hw : |(-469555079/5000000000 : ℝ)|=(469555079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1122855249/2000000000 : ℝ)|^67 ≤ (4684258412613/10000000000000 : ℝ)^51
        have hw : |(1122855249/2000000000 : ℝ)|=(1122855249/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2890845047/5000000000 : ℝ)|^67 ≤ (12171534832061/25000000000000 : ℝ)^51
        have hw : |(2890845047/5000000000 : ℝ)|=(2890845047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s4_s4_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5614726873/10000000000 : ℝ)*x 0 + (-473422347/5000000000 : ℝ)*x 1 + (577686413/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5614726873/10000000000 : ℝ)^67 ≤ (365996277649/781250000000 : ℝ)^51 := by
    have hnat : (5614726873 : ℕ)^67*781250000000^51 ≤ 365996277649^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5614726873 10000000000 365996277649 781250000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (473422347/5000000000 : ℝ)^67 ≤ (903943517023/20000000000000 : ℝ)^51 := by
    have hnat : (473422347 : ℕ)^67*20000000000000^51 ≤ 903943517023^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473422347 5000000000 903943517023 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (577686413/1000000000 : ℝ)^67 ≤ (1945310354519/4000000000000 : ℝ)^51 := by
    have hnat : (577686413 : ℕ)^67*4000000000000^51 ≤ 1945310354519^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      577686413 1000000000 1945310354519 4000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5614726873/10000000000 : ℝ), (-473422347/5000000000 : ℝ), (577686413/1000000000 : ℝ)] ![(365996277649/781250000000 : ℝ), (903943517023/20000000000000 : ℝ), (1945310354519/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5614726873/10000000000 : ℝ)|^67 ≤ (365996277649/781250000000 : ℝ)^51
        have hw : |(5614726873/10000000000 : ℝ)|=(5614726873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-473422347/5000000000 : ℝ)|^67 ≤ (903943517023/20000000000000 : ℝ)^51
        have hw : |(-473422347/5000000000 : ℝ)|=(473422347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(577686413/1000000000 : ℝ)|^67 ≤ (1945310354519/4000000000000 : ℝ)^51
        have hw : |(577686413/1000000000 : ℝ)|=(577686413/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s4_s4_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2838930741/5000000000 : ℝ)*x 0 + (5752046819/10000000000 : ℝ)*x 1 + (-879264647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2838930741/5000000000 : ℝ)^67 ≤ (23770389674163/50000000000000 : ℝ)^51 := by
    have hnat : (2838930741 : ℕ)^67*50000000000000^51 ≤ 23770389674163^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2838930741 5000000000 23770389674163 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5752046819/10000000000 : ℝ)^67 ≤ (12089618308367/25000000000000 : ℝ)^51 := by
    have hnat : (5752046819 : ℕ)^67*25000000000000^51 ≤ 12089618308367^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5752046819 10000000000 12089618308367 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (879264647/10000000000 : ℝ)^67 ≤ (64074178271/1562500000000 : ℝ)^51 := by
    have hnat : (879264647 : ℕ)^67*1562500000000^51 ≤ 64074178271^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      879264647 10000000000 64074178271 1562500000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2838930741/5000000000 : ℝ), (5752046819/10000000000 : ℝ), (-879264647/10000000000 : ℝ)] ![(23770389674163/50000000000000 : ℝ), (12089618308367/25000000000000 : ℝ), (64074178271/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2838930741/5000000000 : ℝ)|^67 ≤ (23770389674163/50000000000000 : ℝ)^51
        have hw : |(2838930741/5000000000 : ℝ)|=(2838930741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5752046819/10000000000 : ℝ)|^67 ≤ (12089618308367/25000000000000 : ℝ)^51
        have hw : |(5752046819/10000000000 : ℝ)|=(5752046819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-879264647/10000000000 : ℝ)|^67 ≤ (64074178271/1562500000000 : ℝ)^51
        have hw : |(-879264647/10000000000 : ℝ)|=(879264647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s4_s4_6 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2268133373/5000000000 : ℝ)*x 0 + (1090691329/2500000000 : ℝ)*x 1 + (512162617/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2268133373/5000000000 : ℝ)^67 ≤ (442492783783/1250000000000 : ℝ)^51 := by
    have hnat : (2268133373 : ℕ)^67*1250000000000^51 ≤ 442492783783^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2268133373 5000000000 442492783783 1250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1090691329/2500000000 : ℝ)^67 ≤ (8407869665981/25000000000000 : ℝ)^51 := by
    have hnat : (1090691329 : ℕ)^67*25000000000000^51 ≤ 8407869665981^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090691329 2500000000 8407869665981 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (512162617/1250000000 : ℝ)^67 ≤ (3871137327031/12500000000000 : ℝ)^51 := by
    have hnat : (512162617 : ℕ)^67*12500000000000^51 ≤ 3871137327031^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512162617 1250000000 3871137327031 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2268133373/5000000000 : ℝ), (1090691329/2500000000 : ℝ), (512162617/1250000000 : ℝ)] ![(442492783783/1250000000000 : ℝ), (8407869665981/25000000000000 : ℝ), (3871137327031/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2268133373/5000000000 : ℝ)|^67 ≤ (442492783783/1250000000000 : ℝ)^51
        have hw : |(2268133373/5000000000 : ℝ)|=(2268133373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1090691329/2500000000 : ℝ)|^67 ≤ (8407869665981/25000000000000 : ℝ)^51
        have hw : |(1090691329/2500000000 : ℝ)|=(1090691329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(512162617/1250000000 : ℝ)|^67 ≤ (3871137327031/12500000000000 : ℝ)^51
        have hw : |(512162617/1250000000 : ℝ)|=(512162617/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s4_s4_7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-463165323/5000000000 : ℝ)*x 0 + (3820296513/10000000000 : ℝ)*x 1 + (7402565451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (463165323/5000000000 : ℝ)^67 ≤ (2195756633399/50000000000000 : ℝ)^51 := by
    have hnat : (463165323 : ℕ)^67*50000000000000^51 ≤ 2195756633399^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      463165323 5000000000 2195756633399 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3820296513/10000000000 : ℝ)^67 ≤ (5649633388033/20000000000000 : ℝ)^51 := by
    have hnat : (3820296513 : ℕ)^67*20000000000000^51 ≤ 5649633388033^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3820296513 10000000000 5649633388033 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7402565451/10000000000 : ℝ)^67 ≤ (1347206395487/2000000000000 : ℝ)^51 := by
    have hnat : (7402565451 : ℕ)^67*2000000000000^51 ≤ 1347206395487^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7402565451 10000000000 1347206395487 2000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-463165323/5000000000 : ℝ), (3820296513/10000000000 : ℝ), (7402565451/10000000000 : ℝ)] ![(2195756633399/50000000000000 : ℝ), (5649633388033/20000000000000 : ℝ), (1347206395487/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-463165323/5000000000 : ℝ)|^67 ≤ (2195756633399/50000000000000 : ℝ)^51
        have hw : |(-463165323/5000000000 : ℝ)|=(463165323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3820296513/10000000000 : ℝ)|^67 ≤ (5649633388033/20000000000000 : ℝ)^51
        have hw : |(3820296513/10000000000 : ℝ)|=(3820296513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7402565451/10000000000 : ℝ)|^67 ≤ (1347206395487/2000000000000 : ℝ)^51
        have hw : |(7402565451/10000000000 : ℝ)|=(7402565451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s4_s4_8 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4220486031/10000000000 : ℝ)*x 0 + (-35774111/2000000000 : ℝ)*x 1 + (924645859/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4220486031/10000000000 : ℝ)^67 ≤ (8049504216639/25000000000000 : ℝ)^51 := by
    have hnat : (4220486031 : ℕ)^67*25000000000000^51 ≤ 8049504216639^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4220486031 10000000000 8049504216639 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35774111/2000000000 : ℝ)^67 ≤ (253096275591/50000000000000 : ℝ)^51 := by
    have hnat : (35774111 : ℕ)^67*50000000000000^51 ≤ 253096275591^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35774111 2000000000 253096275591 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (924645859/1250000000 : ℝ)^67 ≤ (67295790574729/100000000000000 : ℝ)^51 := by
    have hnat : (924645859 : ℕ)^67*100000000000000^51 ≤ 67295790574729^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      924645859 1250000000 67295790574729 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4220486031/10000000000 : ℝ), (-35774111/2000000000 : ℝ), (924645859/1250000000 : ℝ)] ![(8049504216639/25000000000000 : ℝ), (253096275591/50000000000000 : ℝ), (67295790574729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4220486031/10000000000 : ℝ)|^67 ≤ (8049504216639/25000000000000 : ℝ)^51
        have hw : |(4220486031/10000000000 : ℝ)|=(4220486031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-35774111/2000000000 : ℝ)|^67 ≤ (253096275591/50000000000000 : ℝ)^51
        have hw : |(-35774111/2000000000 : ℝ)|=(35774111/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(924645859/1250000000 : ℝ)|^67 ≤ (67295790574729/100000000000000 : ℝ)^51
        have hw : |(924645859/1250000000 : ℝ)|=(924645859/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s4_s4_9 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (989395023/2500000000 : ℝ)*x 0 + (3824364461/5000000000 : ℝ)*x 1 + (-49059641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (989395023/2500000000 : ℝ)^67 ≤ (29589195138459/100000000000000 : ℝ)^51 := by
    have hnat : (989395023 : ℕ)^67*100000000000000^51 ≤ 29589195138459^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      989395023 2500000000 29589195138459 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3824364461/5000000000 : ℝ)^67 ≤ (35159141345153/50000000000000 : ℝ)^51 := by
    have hnat : (3824364461 : ℕ)^67*50000000000000^51 ≤ 35159141345153^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3824364461 5000000000 35159141345153 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (49059641/10000000000 : ℝ)^67 ≤ (23130538531/25000000000000 : ℝ)^51 := by
    have hnat : (49059641 : ℕ)^67*25000000000000^51 ≤ 23130538531^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49059641 10000000000 23130538531 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(989395023/2500000000 : ℝ), (3824364461/5000000000 : ℝ), (-49059641/10000000000 : ℝ)] ![(29589195138459/100000000000000 : ℝ), (35159141345153/50000000000000 : ℝ), (23130538531/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(989395023/2500000000 : ℝ)|^67 ≤ (29589195138459/100000000000000 : ℝ)^51
        have hw : |(989395023/2500000000 : ℝ)|=(989395023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3824364461/5000000000 : ℝ)|^67 ≤ (35159141345153/50000000000000 : ℝ)^51
        have hw : |(3824364461/5000000000 : ℝ)|=(3824364461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-49059641/10000000000 : ℝ)|^67 ≤ (23130538531/25000000000000 : ℝ)^51
        have hw : |(-49059641/10000000000 : ℝ)|=(49059641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s4_s4_13 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (988039879/2500000000 : ℝ)*x 0 + (3368432139/5000000000 : ℝ)*x 1 + (1856606567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (988039879/2500000000 : ℝ)^67 ≤ (7383991171543/25000000000000 : ℝ)^51 := by
    have hnat : (988039879 : ℕ)^67*25000000000000^51 ≤ 7383991171543^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      988039879 2500000000 7383991171543 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3368432139/5000000000 : ℝ)^67 ≤ (11903389160961/20000000000000 : ℝ)^51 := by
    have hnat : (3368432139 : ℕ)^67*20000000000000^51 ≤ 11903389160961^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3368432139 5000000000 11903389160961 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1856606567/10000000000 : ℝ)^67 ≤ (5473544751247/50000000000000 : ℝ)^51 := by
    have hnat : (1856606567 : ℕ)^67*50000000000000^51 ≤ 5473544751247^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1856606567 10000000000 5473544751247 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(988039879/2500000000 : ℝ), (3368432139/5000000000 : ℝ), (1856606567/10000000000 : ℝ)] ![(7383991171543/25000000000000 : ℝ), (11903389160961/20000000000000 : ℝ), (5473544751247/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(988039879/2500000000 : ℝ)|^67 ≤ (7383991171543/25000000000000 : ℝ)^51
        have hw : |(988039879/2500000000 : ℝ)|=(988039879/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3368432139/5000000000 : ℝ)|^67 ≤ (11903389160961/20000000000000 : ℝ)^51
        have hw : |(3368432139/5000000000 : ℝ)|=(3368432139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1856606567/10000000000 : ℝ)|^67 ≤ (5473544751247/50000000000000 : ℝ)^51
        have hw : |(1856606567/10000000000 : ℝ)|=(1856606567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s4_s4_14 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-71796783/5000000000 : ℝ)*x 0 + (1035156899/2500000000 : ℝ)*x 1 + (7474425891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (71796783/5000000000 : ℝ)^67 ≤ (15171944339/4000000000000 : ℝ)^51 := by
    have hnat : (71796783 : ℕ)^67*4000000000000^51 ≤ 15171944339^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71796783 5000000000 15171944339 4000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035156899/2500000000 : ℝ)^67 ≤ (31400030463157/100000000000000 : ℝ)^51 := by
    have hnat : (1035156899 : ℕ)^67*100000000000000^51 ≤ 31400030463157^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035156899 2500000000 31400030463157 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7474425891/10000000000 : ℝ)^67 ≤ (68220670916587/100000000000000 : ℝ)^51 := by
    have hnat : (7474425891 : ℕ)^67*100000000000000^51 ≤ 68220670916587^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7474425891 10000000000 68220670916587 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-71796783/5000000000 : ℝ), (1035156899/2500000000 : ℝ), (7474425891/10000000000 : ℝ)] ![(15171944339/4000000000000 : ℝ), (31400030463157/100000000000000 : ℝ), (68220670916587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-71796783/5000000000 : ℝ)|^67 ≤ (15171944339/4000000000000 : ℝ)^51
        have hw : |(-71796783/5000000000 : ℝ)|=(71796783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035156899/2500000000 : ℝ)|^67 ≤ (31400030463157/100000000000000 : ℝ)^51
        have hw : |(1035156899/2500000000 : ℝ)|=(1035156899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7474425891/10000000000 : ℝ)|^67 ≤ (68220670916587/100000000000000 : ℝ)^51
        have hw : |(7474425891/10000000000 : ℝ)|=(7474425891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s4_s4_15 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3726683331/10000000000 : ℝ)*x 0 + (-944118661/10000000000 : ℝ)*x 1 + (1493790441/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3726683331/10000000000 : ℝ)^67 ≤ (13671162121419/50000000000000 : ℝ)^51 := by
    have hnat : (3726683331 : ℕ)^67*50000000000000^51 ≤ 13671162121419^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3726683331 10000000000 13671162121419 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (944118661/10000000000 : ℝ)^67 ≤ (4502630342923/100000000000000 : ℝ)^51 := by
    have hnat : (944118661 : ℕ)^67*100000000000000^51 ≤ 4502630342923^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      944118661 10000000000 4502630342923 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1493790441/2000000000 : ℝ)^67 ≤ (8519380674671/12500000000000 : ℝ)^51 := by
    have hnat : (1493790441 : ℕ)^67*12500000000000^51 ≤ 8519380674671^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1493790441 2000000000 8519380674671 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3726683331/10000000000 : ℝ), (-944118661/10000000000 : ℝ), (1493790441/2000000000 : ℝ)] ![(13671162121419/50000000000000 : ℝ), (4502630342923/100000000000000 : ℝ), (8519380674671/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3726683331/10000000000 : ℝ)|^67 ≤ (13671162121419/50000000000000 : ℝ)^51
        have hw : |(3726683331/10000000000 : ℝ)|=(3726683331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-944118661/10000000000 : ℝ)|^67 ≤ (4502630342923/100000000000000 : ℝ)^51
        have hw : |(-944118661/10000000000 : ℝ)|=(944118661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1493790441/2000000000 : ℝ)|^67 ≤ (8519380674671/12500000000000 : ℝ)^51
        have hw : |(1493790441/2000000000 : ℝ)|=(1493790441/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s4_s4_16 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (736061899/1000000000 : ℝ)*x 0 + (34374973/80000000 : ℝ)*x 1 + (-79668033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (736061899/1000000000 : ℝ)^67 ≤ (33429661380949/50000000000000 : ℝ)^51 := by
    have hnat : (736061899 : ℕ)^67*50000000000000^51 ≤ 33429661380949^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      736061899 1000000000 33429661380949 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34374973/80000000 : ℝ)^67 ≤ (3296574758167/10000000000000 : ℝ)^51 := by
    have hnat : (34374973 : ℕ)^67*10000000000000^51 ≤ 3296574758167^51*80000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34374973 80000000 3296574758167 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (79668033/10000000000 : ℝ)^67 ≤ (87464823223/50000000000000 : ℝ)^51 := by
    have hnat : (79668033 : ℕ)^67*50000000000000^51 ≤ 87464823223^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79668033 10000000000 87464823223 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(736061899/1000000000 : ℝ), (34374973/80000000 : ℝ), (-79668033/10000000000 : ℝ)] ![(33429661380949/50000000000000 : ℝ), (3296574758167/10000000000000 : ℝ), (87464823223/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(736061899/1000000000 : ℝ)|^67 ≤ (33429661380949/50000000000000 : ℝ)^51
        have hw : |(736061899/1000000000 : ℝ)|=(736061899/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(34374973/80000000 : ℝ)|^67 ≤ (3296574758167/10000000000000 : ℝ)^51
        have hw : |(34374973/80000000 : ℝ)|=(34374973/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-79668033/10000000000 : ℝ)|^67 ≤ (87464823223/50000000000000 : ℝ)^51
        have hw : |(-79668033/10000000000 : ℝ)|=(79668033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s4_s4_20 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1840141359/2500000000 : ℝ)*x 0 + (1596538999/5000000000 : ℝ)*x 1 + (368105067/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1840141359/2500000000 : ℝ)^67 ≤ (8357335462361/12500000000000 : ℝ)^51 := by
    have hnat : (1840141359 : ℕ)^67*12500000000000^51 ≤ 8357335462361^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1840141359 2500000000 8357335462361 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1596538999/5000000000 : ℝ)^67 ≤ (22318624126029/100000000000000 : ℝ)^51 := by
    have hnat : (1596538999 : ℕ)^67*100000000000000^51 ≤ 22318624126029^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1596538999 5000000000 22318624126029 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (368105067/2000000000 : ℝ)^67 ≤ (2705673041309/25000000000000 : ℝ)^51 := by
    have hnat : (368105067 : ℕ)^67*25000000000000^51 ≤ 2705673041309^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      368105067 2000000000 2705673041309 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1840141359/2500000000 : ℝ), (1596538999/5000000000 : ℝ), (368105067/2000000000 : ℝ)] ![(8357335462361/12500000000000 : ℝ), (22318624126029/100000000000000 : ℝ), (2705673041309/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1840141359/2500000000 : ℝ)|^67 ≤ (8357335462361/12500000000000 : ℝ)^51
        have hw : |(1840141359/2500000000 : ℝ)|=(1840141359/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1596538999/5000000000 : ℝ)|^67 ≤ (22318624126029/100000000000000 : ℝ)^51
        have hw : |(1596538999/5000000000 : ℝ)|=(1596538999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(368105067/2000000000 : ℝ)|^67 ≤ (2705673041309/25000000000000 : ℝ)^51
        have hw : |(368105067/2000000000 : ℝ)|=(368105067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s4_s4_21 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1142143/100000000 : ℝ)*x 0 + (343273247/500000000 : ℝ)*x 1 + (4855265483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1142143/100000000 : ℝ)^67 ≤ (140393788311/50000000000000 : ℝ)^51 := by
    have hnat : (1142143 : ℕ)^67*50000000000000^51 ≤ 140393788311^51*100000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1142143 100000000 140393788311 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (343273247/500000000 : ℝ)^67 ≤ (61013951826287/100000000000000 : ℝ)^51 := by
    have hnat : (343273247 : ℕ)^67*100000000000000^51 ≤ 61013951826287^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343273247 500000000 61013951826287 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4855265483/10000000000 : ℝ)^67 ≤ (604769696723/1562500000000 : ℝ)^51 := by
    have hnat : (4855265483 : ℕ)^67*1562500000000^51 ≤ 604769696723^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4855265483 10000000000 604769696723 1562500000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1142143/100000000 : ℝ), (343273247/500000000 : ℝ), (4855265483/10000000000 : ℝ)] ![(140393788311/50000000000000 : ℝ), (61013951826287/100000000000000 : ℝ), (604769696723/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1142143/100000000 : ℝ)|^67 ≤ (140393788311/50000000000000 : ℝ)^51
        have hw : |(-1142143/100000000 : ℝ)|=(1142143/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(343273247/500000000 : ℝ)|^67 ≤ (61013951826287/100000000000000 : ℝ)^51
        have hw : |(343273247/500000000 : ℝ)|=(343273247/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4855265483/10000000000 : ℝ)|^67 ≤ (604769696723/1562500000000 : ℝ)^51
        have hw : |(4855265483/10000000000 : ℝ)|=(4855265483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s4_s4_22 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3665840623/5000000000 : ℝ)*x 0 + (-36057721/5000000000 : ℝ)*x 1 + (135412257/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3665840623/5000000000 : ℝ)^67 ≤ (16628554931229/25000000000000 : ℝ)^51 := by
    have hnat : (3665840623 : ℕ)^67*25000000000000^51 ≤ 16628554931229^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3665840623 5000000000 16628554931229 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (36057721/5000000000 : ℝ)^67 ≤ (38368705521/25000000000000 : ℝ)^51 := by
    have hnat : (36057721 : ℕ)^67*25000000000000^51 ≤ 38368705521^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36057721 5000000000 38368705521 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135412257/312500000 : ℝ)^67 ≤ (16666152719599/50000000000000 : ℝ)^51 := by
    have hnat : (135412257 : ℕ)^67*50000000000000^51 ≤ 16666152719599^51*312500000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135412257 312500000 16666152719599 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3665840623/5000000000 : ℝ), (-36057721/5000000000 : ℝ), (135412257/312500000 : ℝ)] ![(16628554931229/25000000000000 : ℝ), (38368705521/25000000000000 : ℝ), (16666152719599/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3665840623/5000000000 : ℝ)|^67 ≤ (16628554931229/25000000000000 : ℝ)^51
        have hw : |(3665840623/5000000000 : ℝ)|=(3665840623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-36057721/5000000000 : ℝ)|^67 ≤ (38368705521/25000000000000 : ℝ)^51
        have hw : |(-36057721/5000000000 : ℝ)|=(36057721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135412257/312500000 : ℝ)|^67 ≤ (16666152719599/50000000000000 : ℝ)^51
        have hw : |(135412257/312500000 : ℝ)|=(135412257/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s4_s4_23 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3688314603/10000000000 : ℝ)*x 0 + (376928921/500000000 : ℝ)*x 1 + (-868671441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3688314603/10000000000 : ℝ)^67 ≤ (13486549515357/50000000000000 : ℝ)^51 := by
    have hnat : (3688314603 : ℕ)^67*50000000000000^51 ≤ 13486549515357^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3688314603 10000000000 13486549515357 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (376928921/500000000 : ℝ)^67 ≤ (68990935142487/100000000000000 : ℝ)^51 := by
    have hnat : (376928921 : ℕ)^67*100000000000000^51 ≤ 68990935142487^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      376928921 500000000 68990935142487 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (868671441/10000000000 : ℝ)^67 ≤ (1008991453251/25000000000000 : ℝ)^51 := by
    have hnat : (868671441 : ℕ)^67*25000000000000^51 ≤ 1008991453251^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868671441 10000000000 1008991453251 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3688314603/10000000000 : ℝ), (376928921/500000000 : ℝ), (-868671441/10000000000 : ℝ)] ![(13486549515357/50000000000000 : ℝ), (68990935142487/100000000000000 : ℝ), (1008991453251/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3688314603/10000000000 : ℝ)|^67 ≤ (13486549515357/50000000000000 : ℝ)^51
        have hw : |(3688314603/10000000000 : ℝ)|=(3688314603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(376928921/500000000 : ℝ)|^67 ≤ (68990935142487/100000000000000 : ℝ)^51
        have hw : |(376928921/500000000 : ℝ)|=(376928921/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-868671441/10000000000 : ℝ)|^67 ≤ (1008991453251/25000000000000 : ℝ)^51
        have hw : |(-868671441/10000000000 : ℝ)|=(868671441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s4_s4_27 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1499792017/2000000000 : ℝ)*x 0 + (2663091331/10000000000 : ℝ)*x 1 + (2226866811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1499792017/2000000000 : ℝ)^67 ≤ (2141093851193/3125000000000 : ℝ)^51 := by
    have hnat : (1499792017 : ℕ)^67*3125000000000^51 ≤ 2141093851193^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1499792017 2000000000 2141093851193 3125000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2663091331/10000000000 : ℝ)^67 ≤ (2197986568249/12500000000000 : ℝ)^51 := by
    have hnat : (2663091331 : ℕ)^67*12500000000000^51 ≤ 2197986568249^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2663091331 10000000000 2197986568249 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2226866811/10000000000 : ℝ)^67 ≤ (3475276053327/25000000000000 : ℝ)^51 := by
    have hnat : (2226866811 : ℕ)^67*25000000000000^51 ≤ 3475276053327^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2226866811 10000000000 3475276053327 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1499792017/2000000000 : ℝ), (2663091331/10000000000 : ℝ), (2226866811/10000000000 : ℝ)] ![(2141093851193/3125000000000 : ℝ), (2197986568249/12500000000000 : ℝ), (3475276053327/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1499792017/2000000000 : ℝ)|^67 ≤ (2141093851193/3125000000000 : ℝ)^51
        have hw : |(1499792017/2000000000 : ℝ)|=(1499792017/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2663091331/10000000000 : ℝ)|^67 ≤ (2197986568249/12500000000000 : ℝ)^51
        have hw : |(2663091331/10000000000 : ℝ)|=(2663091331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2226866811/10000000000 : ℝ)|^67 ≤ (3475276053327/25000000000000 : ℝ)^51
        have hw : |(2226866811/10000000000 : ℝ)|=(2226866811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c305063_s4 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev3 : (0 : ℝ) ≤ ((37309/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(37309/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(74933/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(74933/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(72141/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(72141/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((16351/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16351/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(66141/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(66141/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15883/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15883/25000 : ℝ)*X 1 2) := by
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
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  rcases hprev3 with ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩
  have s4_pow0 : (37309/50000 : ℝ) ^ (133/32 : ℝ) ≤ (2961462452547471607/10000000000000000000 : ℝ) := by
    have hpowers : (37309/50000 : ℝ)^133 ≤ (2961462452547471607/10000000000000000000 : ℝ)^32 := by
      have hnat : (37309 : ℕ)^133*10000000000000000000^32 ≤ 2961462452547471607^32*50000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37309 50000 2961462452547471607 10000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (37309/50000 : ℝ)) (X := (2961462452547471607/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s4_corner0a : (12961462452547471607/10000000000000000000 : ℝ) ≤ (10643996504914153/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (12961462452547471607/10000000000000000000 : ℝ)^32 ≤ (10643996504914153/10000000000000000 : ℝ)^133 := by
      have hnat : (12961462452547471607 : ℕ)^32*10000000000000000^133 ≤ 10643996504914153^133*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12961462452547471607 10000000000000000000 10643996504914153 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10643996504914153/10000000000000000 : ℝ)) (X := (12961462452547471607/10000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s4_corner0b : (7961462452547471607/5000000000000000000 : ℝ) ≤ (11184253464397801/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (7961462452547471607/5000000000000000000 : ℝ)^32 ≤ (11184253464397801/10000000000000000 : ℝ)^133 := by
      have hnat : (7961462452547471607 : ℕ)^32*10000000000000000^133 ≤ 11184253464397801^133*5000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7961462452547471607 5000000000000000000 11184253464397801 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11184253464397801/10000000000000000 : ℝ)) (X := (7961462452547471607/5000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s4_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(643996504914153/7461800000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(2110378747983/29147656250000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (37309/50000 : ℝ)) (alpha := (643996504914153/7461800000000000 : ℝ)) (beta := (2110378747983/29147656250000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow0,s4_corner0a]) (by linarith only [s4_pow0,s4_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (37309/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(643996504914153/7461800000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(2110378747983/29147656250000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow1 : (74933/100000 : ℝ) ^ (133/32 : ℝ) ≤ (15068851756025300351/50000000000000000000 : ℝ) := by
    have hpowers : (74933/100000 : ℝ)^133 ≤ (15068851756025300351/50000000000000000000 : ℝ)^32 := by
      have hnat : (74933 : ℕ)^133*50000000000000000000^32 ≤ 15068851756025300351^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        74933 100000 15068851756025300351 50000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (74933/100000 : ℝ)) (X := (15068851756025300351/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s4_corner1a : (65068851756025300351/50000000000000000000 : ℝ) ≤ (1065431584457137/1000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (65068851756025300351/50000000000000000000 : ℝ)^32 ≤ (1065431584457137/1000000000000000 : ℝ)^133 := by
      have hnat : (65068851756025300351 : ℕ)^32*1000000000000000^133 ≤ 1065431584457137^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        65068851756025300351 50000000000000000000 1065431584457137 1000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1065431584457137/1000000000000000 : ℝ)) (X := (65068851756025300351/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s4_corner1b : (40068851756025300351/25000000000000000000 : ℝ) ≤ (11201889426178307/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (40068851756025300351/25000000000000000000 : ℝ)^32 ≤ (11201889426178307/10000000000000000 : ℝ)^133 := by
      have hnat : (40068851756025300351 : ℕ)^32*10000000000000000^133 ≤ 11201889426178307^133*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40068851756025300351 25000000000000000000 11201889426178307 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11201889426178307/10000000000000000 : ℝ)) (X := (40068851756025300351/25000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s4_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(65431584457137/749330000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(547573581606937/7493300000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (74933/100000 : ℝ)) (alpha := (65431584457137/749330000000000 : ℝ)) (beta := (547573581606937/7493300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow1,s4_corner1a]) (by linarith only [s4_pow1,s4_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (74933/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(65431584457137/749330000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(547573581606937/7493300000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow2 : (72141/100000 : ℝ) ^ (133/32 : ℝ) ≤ (25737691715087695593/100000000000000000000 : ℝ) := by
    have hpowers : (72141/100000 : ℝ)^133 ≤ (25737691715087695593/100000000000000000000 : ℝ)^32 := by
      have hnat : (72141 : ℕ)^133*100000000000000000000^32 ≤ 25737691715087695593^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        72141 100000 25737691715087695593 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (72141/100000 : ℝ)) (X := (25737691715087695593/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s4_corner2a : (125737691715087695593/100000000000000000000 : ℝ) ≤ (5283254713861223/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (125737691715087695593/100000000000000000000 : ℝ)^32 ≤ (5283254713861223/5000000000000000 : ℝ)^133 := by
      have hnat : (125737691715087695593 : ℕ)^32*5000000000000000^133 ≤ 5283254713861223^133*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        125737691715087695593 100000000000000000000 5283254713861223 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5283254713861223/5000000000000000 : ℝ)) (X := (125737691715087695593/100000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s4_corner2b : (75737691715087695593/50000000000000000000 : ℝ) ≤ (5525359948185881/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (75737691715087695593/50000000000000000000 : ℝ)^32 ≤ (5525359948185881/5000000000000000 : ℝ)^133 := by
      have hnat : (75737691715087695593 : ℕ)^32*5000000000000000^133 ≤ 5525359948185881^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        75737691715087695593 50000000000000000000 5525359948185881 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5525359948185881/5000000000000000 : ℝ)) (X := (75737691715087695593/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s4_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(94418237953741/1202350000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(40350872387443/601175000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (72141/100000 : ℝ)) (alpha := (94418237953741/1202350000000000 : ℝ)) (beta := (40350872387443/601175000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow2,s4_corner2a]) (by linarith only [s4_pow2,s4_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (72141/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(94418237953741/1202350000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(40350872387443/601175000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s4_0 : ((-469555079/5000000000 : ℝ)*X 0 0+(1122855249/2000000000 : ℝ)*X 0 1+(2890845047/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s4_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_1 : ((5614726873/10000000000 : ℝ)*X 1 0+(-473422347/5000000000 : ℝ)*X 1 1+(577686413/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s4_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_2 : ((2838930741/5000000000 : ℝ)*X 2 0+(5752046819/10000000000 : ℝ)*X 2 1+(-879264647/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s4_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_6 : ((2268133373/5000000000 : ℝ)*X 0 0+(1090691329/2500000000 : ℝ)*X 0 1+(512162617/1250000000 : ℝ)*X 0 2+(2268133373/5000000000 : ℝ)*X 1 0+(1090691329/2500000000 : ℝ)*X 1 1+(512162617/1250000000 : ℝ)*X 1 2+(2268133373/5000000000 : ℝ)*X 2 0+(1090691329/2500000000 : ℝ)*X 2 1+(512162617/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s4_s4_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_7 : ((-463165323/5000000000 : ℝ)*X 0 0+(3820296513/10000000000 : ℝ)*X 0 1+(7402565451/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s4_s4_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_8 : ((4220486031/10000000000 : ℝ)*X 1 0+(-35774111/2000000000 : ℝ)*X 1 1+(924645859/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s4_s4_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_9 : ((989395023/2500000000 : ℝ)*X 2 0+(3824364461/5000000000 : ℝ)*X 2 1+(-49059641/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s4_s4_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_13 : ((988039879/2500000000 : ℝ)*X 0 0+(3368432139/5000000000 : ℝ)*X 0 1+(1856606567/10000000000 : ℝ)*X 0 2+(988039879/2500000000 : ℝ)*X 1 0+(3368432139/5000000000 : ℝ)*X 1 1+(1856606567/10000000000 : ℝ)*X 1 2+(988039879/2500000000 : ℝ)*X 2 0+(3368432139/5000000000 : ℝ)*X 2 1+(1856606567/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s4_s4_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_14 : ((-71796783/5000000000 : ℝ)*X 0 0+(1035156899/2500000000 : ℝ)*X 0 1+(7474425891/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s4_s4_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_15 : ((3726683331/10000000000 : ℝ)*X 1 0+(-944118661/10000000000 : ℝ)*X 1 1+(1493790441/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s4_s4_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_16 : ((736061899/1000000000 : ℝ)*X 2 0+(34374973/80000000 : ℝ)*X 2 1+(-79668033/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s4_s4_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_20 : ((1840141359/2500000000 : ℝ)*X 0 0+(1596538999/5000000000 : ℝ)*X 0 1+(368105067/2000000000 : ℝ)*X 0 2+(1840141359/2500000000 : ℝ)*X 1 0+(1596538999/5000000000 : ℝ)*X 1 1+(368105067/2000000000 : ℝ)*X 1 2+(1840141359/2500000000 : ℝ)*X 2 0+(1596538999/5000000000 : ℝ)*X 2 1+(368105067/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s4_s4_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_21 : ((-1142143/100000000 : ℝ)*X 0 0+(343273247/500000000 : ℝ)*X 0 1+(4855265483/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s4_s4_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_22 : ((3665840623/5000000000 : ℝ)*X 1 0+(-36057721/5000000000 : ℝ)*X 1 1+(135412257/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s4_s4_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_23 : ((3688314603/10000000000 : ℝ)*X 2 0+(376928921/500000000 : ℝ)*X 2 1+(-868671441/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s4_s4_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_27 : ((1499792017/2000000000 : ℝ)*X 0 0+(2663091331/10000000000 : ℝ)*X 0 1+(2226866811/10000000000 : ℝ)*X 0 2+(1499792017/2000000000 : ℝ)*X 1 0+(2663091331/10000000000 : ℝ)*X 1 1+(2226866811/10000000000 : ℝ)*X 1 2+(1499792017/2000000000 : ℝ)*X 2 0+(2663091331/10000000000 : ℝ)*X 2 1+(2226866811/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s4_s4_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s4_0 : (0 : ℝ) ≤ ((16351/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16351/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1901267651452154900053287562443/168069009667397500000000000000000000 : ℝ) := by norm_num
    linear_combination (390889778703/1000000000000 : ℝ)*(base7) + (337609/250000000000 : ℝ)*(base50) + (49919711519/500000000000 : ℝ)*(base60) + (240462239697/100000000000 : ℝ)*(major_s4_0) + (240462239697/100000000000 : ℝ)*(major_s4_1) + (240462239697/100000000000 : ℝ)*(major_s4_2) + (11262803/1000000000000 : ℝ)*(sp_s4_0) + (288543/250000000000 : ℝ)*(sp_s4_6) + (2993248347719/1000000000000 : ℝ)*(sp_s4_7) + (2993335169273/1000000000000 : ℝ)*(sp_s4_8) + (598667187151/200000000000 : ℝ)*(sp_s4_9) + (981638598783/500000000000 : ℝ)*(sp_s4_13) + (4770327/62500000000 : ℝ)*(sp_s4_14) + (766481/1000000000000 : ℝ)*(sp_s4_15) + (314477714607/200000000000 : ℝ)*(f.failure) + (598667187151/200000000000 : ℝ)*(f.sum) + (623340725136047399/4504784627500000000000000000000 : ℝ)*base62 + (39653924812477/120235000000000000000000000 : ℝ)*base64 + (22141093106913/187332500000000000000000000 : ℝ)*base66 + (3978571676451/12023500000000000000000000 : ℝ)*base68 + (1400401480063701637/3588678092000000000000000000000 : ℝ)*base70 + (43325334069653/373090000000000000000000000 : ℝ)*base73 + (157208918536317/374665000000000000000000000 : ℝ)*base74 + (652107051026939/746180000000000000000000000 : ℝ)*base76 + (5777537311440385149/13978376485000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (603/625000000000000 : ℝ)*base87 + (603/625000000000000 : ℝ)*base89 + (603/625000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s4_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(66141/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(66141/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (11448354442873112538631918845147/672276038669590000000000000000000000 : ℝ) := by norm_num
    linear_combination (108395321353/250000000000 : ℝ)*(base7) + (1503621/1000000000000 : ℝ)*(base49) + (228607535369/100000000000 : ℝ)*(major_s4_0) + (228607535369/100000000000 : ℝ)*(major_s4_1) + (228607535369/100000000000 : ℝ)*(major_s4_2) + (186127/250000000000 : ℝ)*(sp_s4_0) + (1169791/250000000000 : ℝ)*(sp_s4_1) + (62941/1000000000000 : ℝ)*(sp_s4_7) + (45928977/500000000000 : ℝ)*(sp_s4_8) + (1403580694039/500000000000 : ℝ)*(sp_s4_14) + (2807065658409/1000000000000 : ℝ)*(sp_s4_15) + (2807162195527/1000000000000 : ℝ)*(sp_s4_16) + (77134797143/40000000000 : ℝ)*(sp_s4_20) + (40861541/500000000000 : ℝ)*(sp_s4_27) + (298974073249/200000000000 : ℝ)*(f.failure) + (2807162195527/1000000000000 : ℝ)*(f.sum) + (1543480347680046787/4504784627500000000000000000000 : ℝ)*base62 + (156629206601763/240470000000000000000000000 : ℝ)*base64 + (630635115606791/749330000000000000000000000 : ℝ)*base66 + (187631945656507/240470000000000000000000000 : ℝ)*base68 + (3457587531341536519/17943390460000000000000000000000 : ℝ)*base70 + (60938896603641/93272500000000000000000000 : ℝ)*base72 + (62702980559667/74933000000000000000000000 : ℝ)*base74 + (467370247095349/746180000000000000000000000 : ℝ)*base76 + (11790014579010963667/27956752970000000000000000000000 : ℝ)*base78 + (721/625000000000000 : ℝ)*base87 + (721/625000000000000 : ℝ)*base89 + (721/625000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s4_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15883/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15883/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (452491162072053498919392153/45047846275000000000000000000000 : ℝ) := by norm_num
    linear_combination (53027235739/125000000000 : ℝ)*(base7) + (69525076003/500000000000 : ℝ)*(base40) + (1225889/1000000000000 : ℝ)*(base49) + (548999267459/250000000000 : ℝ)*(major_s4_0) + (548999267459/250000000000 : ℝ)*(major_s4_1) + (548999267459/250000000000 : ℝ)*(major_s4_2) + (10533723/1000000000000 : ℝ)*(sp_s4_1) + (4179299/200000000000 : ℝ)*(sp_s4_2) + (16344553/200000000000 : ℝ)*(sp_s4_9) + (3096131/200000000000 : ℝ)*(sp_s4_20) + (538348716149/200000000000 : ℝ)*(sp_s4_21) + (1345866523511/500000000000 : ℝ)*(sp_s4_22) + (538328192297/200000000000 : ℝ)*(sp_s4_23) + (465042589347/250000000000 : ℝ)*(sp_s4_27) + (358991988033/250000000000 : ℝ)*(f.failure) + (538348716149/200000000000 : ℝ)*(f.sum) + (11082218455424228957/22523923137500000000000000000000 : ℝ)*base63 + (12876833680233/601175000000000000000000000 : ℝ)*base65 + (561894991691477/1873325000000000000000000000 : ℝ)*base66 + (338308718090991/1202350000000000000000000000 : ℝ)*base69 + (1677073959400354053/44858476150000000000000000000000 : ℝ)*base71 + (133428611393437/1865450000000000000000000000 : ℝ)*base73 + (276455176031527/749330000000000000000000000 : ℝ)*base75 + (108386365721079/932725000000000000000000000 : ℝ)*base76 + (323682663119043499/6989188242500000000000000000000 : ℝ)*base78 + (83/195312500000000 : ℝ)*base87 + (83/195312500000000 : ℝ)*base89 + (83/195312500000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev3 : (0 : ℝ) ≤ ((37309/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(37309/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(74933/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(74933/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(72141/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(72141/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((16351/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16351/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(66141/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(66141/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15883/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15883/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c305063_s4 p hpa hpb X hX hprev3

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c310063_s4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:28:15.014351+00:00
-- url     : https://prove2.me/submissions/074470a3-e9bc-4d49-9114-d928ddf3f70c

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
theorem collision_support_c310063_s4_s4_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1645710499/10000000000 : ℝ)*x 0 + (336687969/625000000 : ℝ)*x 1 + (541182049/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1645710499/10000000000 : ℝ)^71 ≤ (4868033247419/50000000000000 : ℝ)^55 := by
    have hnat : (1645710499 : ℕ)^71*50000000000000^55 ≤ 4868033247419^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1645710499 10000000000 4868033247419 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336687969/625000000 : ℝ)^71 ≤ (44998097189637/100000000000000 : ℝ)^55 := by
    have hnat : (336687969 : ℕ)^71*100000000000000^55 ≤ 44998097189637^55*625000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336687969 625000000 44998097189637 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541182049/1000000000 : ℝ)^71 ≤ (9053167259481/20000000000000 : ℝ)^55 := by
    have hnat : (541182049 : ℕ)^71*20000000000000^55 ≤ 9053167259481^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541182049 1000000000 9053167259481 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1645710499/10000000000 : ℝ), (336687969/625000000 : ℝ), (541182049/1000000000 : ℝ)] ![(4868033247419/50000000000000 : ℝ), (44998097189637/100000000000000 : ℝ), (9053167259481/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1645710499/10000000000 : ℝ)|^71 ≤ (4868033247419/50000000000000 : ℝ)^55
        have hw : |(-1645710499/10000000000 : ℝ)|=(1645710499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(336687969/625000000 : ℝ)|^71 ≤ (44998097189637/100000000000000 : ℝ)^55
        have hw : |(336687969/625000000 : ℝ)|=(336687969/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541182049/1000000000 : ℝ)|^71 ≤ (9053167259481/20000000000000 : ℝ)^55
        have hw : |(541182049/1000000000 : ℝ)|=(541182049/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310063_s4_s4_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5387965847/10000000000 : ℝ)*x 0 + (-206725649/1250000000 : ℝ)*x 1 + (2702566371/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5387965847/10000000000 : ℝ)^71 ≤ (45008431332007/100000000000000 : ℝ)^55 := by
    have hnat : (5387965847 : ℕ)^71*100000000000000^55 ≤ 45008431332007^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387965847 10000000000 45008431332007 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (206725649/1250000000 : ℝ)^71 ≤ (9797930263647/100000000000000 : ℝ)^55 := by
    have hnat : (206725649 : ℕ)^71*100000000000000^55 ≤ 9797930263647^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206725649 1250000000 9797930263647 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2702566371/5000000000 : ℝ)^71 ≤ (45193638386379/100000000000000 : ℝ)^55 := by
    have hnat : (2702566371 : ℕ)^71*100000000000000^55 ≤ 45193638386379^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702566371 5000000000 45193638386379 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5387965847/10000000000 : ℝ), (-206725649/1250000000 : ℝ), (2702566371/5000000000 : ℝ)] ![(45008431332007/100000000000000 : ℝ), (9797930263647/100000000000000 : ℝ), (45193638386379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5387965847/10000000000 : ℝ)|^71 ≤ (45008431332007/100000000000000 : ℝ)^55
        have hw : |(5387965847/10000000000 : ℝ)|=(5387965847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-206725649/1250000000 : ℝ)|^71 ≤ (9797930263647/100000000000000 : ℝ)^55
        have hw : |(-206725649/1250000000 : ℝ)|=(206725649/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2702566371/5000000000 : ℝ)|^71 ≤ (45193638386379/100000000000000 : ℝ)^55
        have hw : |(2702566371/5000000000 : ℝ)|=(2702566371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310063_s4_s4_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5406766497/10000000000 : ℝ)*x 0 + (1350361603/2500000000 : ℝ)*x 1 + (-408111151/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5406766497/10000000000 : ℝ)^71 ≤ (22605636635513/50000000000000 : ℝ)^55 := by
    have hnat : (5406766497 : ℕ)^71*50000000000000^55 ≤ 22605636635513^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406766497 10000000000 22605636635513 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1350361603/2500000000 : ℝ)^71 ≤ (45153853536773/100000000000000 : ℝ)^55 := by
    have hnat : (1350361603 : ℕ)^71*100000000000000^55 ≤ 45153853536773^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350361603 2500000000 45153853536773 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (408111151/2500000000 : ℝ)^71 ≤ (9634873179321/100000000000000 : ℝ)^55 := by
    have hnat : (408111151 : ℕ)^71*100000000000000^55 ≤ 9634873179321^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408111151 2500000000 9634873179321 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5406766497/10000000000 : ℝ), (1350361603/2500000000 : ℝ), (-408111151/2500000000 : ℝ)] ![(22605636635513/50000000000000 : ℝ), (45153853536773/100000000000000 : ℝ), (9634873179321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5406766497/10000000000 : ℝ)|^71 ≤ (22605636635513/50000000000000 : ℝ)^55
        have hw : |(5406766497/10000000000 : ℝ)|=(5406766497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1350361603/2500000000 : ℝ)|^71 ≤ (45153853536773/100000000000000 : ℝ)^55
        have hw : |(1350361603/2500000000 : ℝ)|=(1350361603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-408111151/2500000000 : ℝ)|^71 ≤ (9634873179321/100000000000000 : ℝ)^55
        have hw : |(-408111151/2500000000 : ℝ)|=(408111151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310063_s4_s4_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (171112921/400000000 : ℝ)*x 0 + (4273707883/10000000000 : ℝ)*x 1 + (1064402617/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (171112921/400000000 : ℝ)^71 ≤ (3341505479893/10000000000000 : ℝ)^55 := by
    have hnat : (171112921 : ℕ)^71*10000000000000^55 ≤ 3341505479893^55*400000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171112921 400000000 3341505479893 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4273707883/10000000000 : ℝ)^71 ≤ (33373565216569/100000000000000 : ℝ)^55 := by
    have hnat : (4273707883 : ℕ)^71*100000000000000^55 ≤ 33373565216569^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4273707883 10000000000 33373565216569 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1064402617/2500000000 : ℝ)^71 ≤ (16605689983279/50000000000000 : ℝ)^55 := by
    have hnat : (1064402617 : ℕ)^71*50000000000000^55 ≤ 16605689983279^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064402617 2500000000 16605689983279 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(171112921/400000000 : ℝ), (4273707883/10000000000 : ℝ), (1064402617/2500000000 : ℝ)] ![(3341505479893/10000000000000 : ℝ), (33373565216569/100000000000000 : ℝ), (16605689983279/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(171112921/400000000 : ℝ)|^71 ≤ (3341505479893/10000000000000 : ℝ)^55
        have hw : |(171112921/400000000 : ℝ)|=(171112921/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4273707883/10000000000 : ℝ)|^71 ≤ (33373565216569/100000000000000 : ℝ)^55
        have hw : |(4273707883/10000000000 : ℝ)|=(4273707883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1064402617/2500000000 : ℝ)|^71 ≤ (16605689983279/50000000000000 : ℝ)^55
        have hw : |(1064402617/2500000000 : ℝ)|=(1064402617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310063_s4_s4_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-760403843/5000000000 : ℝ)*x 0 + (915015097/2000000000 : ℝ)*x 1 + (6272361949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (760403843/5000000000 : ℝ)^71 ≤ (2198225721379/25000000000000 : ℝ)^55 := by
    have hnat : (760403843 : ℕ)^71*25000000000000^55 ≤ 2198225721379^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      760403843 5000000000 2198225721379 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (915015097/2000000000 : ℝ)^71 ≤ (18221118645081/50000000000000 : ℝ)^55 := by
    have hnat : (915015097 : ℕ)^71*50000000000000^55 ≤ 18221118645081^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      915015097 2000000000 18221118645081 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6272361949/10000000000 : ℝ)^71 ≤ (54764859817093/100000000000000 : ℝ)^55 := by
    have hnat : (6272361949 : ℕ)^71*100000000000000^55 ≤ 54764859817093^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6272361949 10000000000 54764859817093 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-760403843/5000000000 : ℝ), (915015097/2000000000 : ℝ), (6272361949/10000000000 : ℝ)] ![(2198225721379/25000000000000 : ℝ), (18221118645081/50000000000000 : ℝ), (54764859817093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-760403843/5000000000 : ℝ)|^71 ≤ (2198225721379/25000000000000 : ℝ)^55
        have hw : |(-760403843/5000000000 : ℝ)|=(760403843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(915015097/2000000000 : ℝ)|^71 ≤ (18221118645081/50000000000000 : ℝ)^55
        have hw : |(915015097/2000000000 : ℝ)|=(915015097/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6272361949/10000000000 : ℝ)|^71 ≤ (54764859817093/100000000000000 : ℝ)^55
        have hw : |(6272361949/10000000000 : ℝ)|=(6272361949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310063_s4_s4_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5014092143/10000000000 : ℝ)*x 0 + (-872734803/10000000000 : ℝ)*x 1 + (3132804491/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5014092143/10000000000 : ℝ)^71 ≤ (2563631183561/6250000000000 : ℝ)^55 := by
    have hnat : (5014092143 : ℕ)^71*6250000000000^55 ≤ 2563631183561^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5014092143 10000000000 2563631183561 6250000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (872734803/10000000000 : ℝ)^71 ≤ (536642840227/12500000000000 : ℝ)^55 := by
    have hnat : (872734803 : ℕ)^71*12500000000000^55 ≤ 536642840227^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872734803 10000000000 536642840227 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3132804491/5000000000 : ℝ)^71 ≤ (54688758333663/100000000000000 : ℝ)^55 := by
    have hnat : (3132804491 : ℕ)^71*100000000000000^55 ≤ 54688758333663^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3132804491 5000000000 54688758333663 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5014092143/10000000000 : ℝ), (-872734803/10000000000 : ℝ), (3132804491/5000000000 : ℝ)] ![(2563631183561/6250000000000 : ℝ), (536642840227/12500000000000 : ℝ), (54688758333663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5014092143/10000000000 : ℝ)|^71 ≤ (2563631183561/6250000000000 : ℝ)^55
        have hw : |(5014092143/10000000000 : ℝ)|=(5014092143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-872734803/10000000000 : ℝ)|^71 ≤ (536642840227/12500000000000 : ℝ)^55
        have hw : |(-872734803/10000000000 : ℝ)|=(872734803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3132804491/5000000000 : ℝ)|^71 ≤ (54688758333663/100000000000000 : ℝ)^55
        have hw : |(3132804491/5000000000 : ℝ)|=(3132804491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310063_s4_s4_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4803227149/10000000000 : ℝ)*x 0 + (3239880199/5000000000 : ℝ)*x 1 + (-419594931/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4803227149/10000000000 : ℝ)^71 ≤ (9701261806369/25000000000000 : ℝ)^55 := by
    have hnat : (4803227149 : ℕ)^71*25000000000000^55 ≤ 9701261806369^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4803227149 10000000000 9701261806369 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3239880199/5000000000 : ℝ)^71 ≤ (11422725163857/20000000000000 : ℝ)^55 := by
    have hnat : (3239880199 : ℕ)^71*20000000000000^55 ≤ 11422725163857^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3239880199 5000000000 11422725163857 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (419594931/5000000000 : ℝ)^71 ≤ (408132694157/10000000000000 : ℝ)^55 := by
    have hnat : (419594931 : ℕ)^71*10000000000000^55 ≤ 408132694157^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419594931 5000000000 408132694157 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4803227149/10000000000 : ℝ), (3239880199/5000000000 : ℝ), (-419594931/5000000000 : ℝ)] ![(9701261806369/25000000000000 : ℝ), (11422725163857/20000000000000 : ℝ), (408132694157/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4803227149/10000000000 : ℝ)|^71 ≤ (9701261806369/25000000000000 : ℝ)^55
        have hw : |(4803227149/10000000000 : ℝ)|=(4803227149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3239880199/5000000000 : ℝ)|^71 ≤ (11422725163857/20000000000000 : ℝ)^55
        have hw : |(3239880199/5000000000 : ℝ)|=(3239880199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-419594931/5000000000 : ℝ)|^71 ≤ (408132694157/10000000000000 : ℝ)^55
        have hw : |(-419594931/5000000000 : ℝ)|=(419594931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310063_s4_s4_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (89546447/200000000 : ℝ)*x 0 + (5690220907/10000000000 : ℝ)*x 1 + (489828343/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (89546447/200000000 : ℝ)^71 ≤ (7088044377429/20000000000000 : ℝ)^55 := by
    have hnat : (89546447 : ℕ)^71*20000000000000^55 ≤ 7088044377429^55*200000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89546447 200000000 7088044377429 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5690220907/10000000000 : ℝ)^71 ≤ (24147043711347/50000000000000 : ℝ)^55 := by
    have hnat : (5690220907 : ℕ)^71*50000000000000^55 ≤ 24147043711347^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5690220907 10000000000 24147043711347 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (489828343/2000000000 : ℝ)^71 ≤ (16265690676153/100000000000000 : ℝ)^55 := by
    have hnat : (489828343 : ℕ)^71*100000000000000^55 ≤ 16265690676153^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489828343 2000000000 16265690676153 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(89546447/200000000 : ℝ), (5690220907/10000000000 : ℝ), (489828343/2000000000 : ℝ)] ![(7088044377429/20000000000000 : ℝ), (24147043711347/50000000000000 : ℝ), (16265690676153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(89546447/200000000 : ℝ)|^71 ≤ (7088044377429/20000000000000 : ℝ)^55
        have hw : |(89546447/200000000 : ℝ)|=(89546447/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5690220907/10000000000 : ℝ)|^71 ≤ (24147043711347/50000000000000 : ℝ)^55
        have hw : |(5690220907/10000000000 : ℝ)|=(5690220907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(489828343/2000000000 : ℝ)|^71 ≤ (16265690676153/100000000000000 : ℝ)^55
        have hw : |(489828343/2000000000 : ℝ)|=(489828343/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310063_s4_s4_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-864458459/10000000000 : ℝ)*x 0 + (5023793103/10000000000 : ℝ)*x 1 + (6261171851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (864458459/10000000000 : ℝ)^71 ≤ (16565073379/390625000000 : ℝ)^55 := by
    have hnat : (864458459 : ℕ)^71*390625000000^55 ≤ 16565073379^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864458459 10000000000 16565073379 390625000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5023793103/10000000000 : ℝ)^71 ≤ (41120573419851/100000000000000 : ℝ)^55 := by
    have hnat : (5023793103 : ℕ)^71*100000000000000^55 ≤ 41120573419851^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5023793103 10000000000 41120573419851 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6261171851/10000000000 : ℝ)^71 ≤ (27319383890403/50000000000000 : ℝ)^55 := by
    have hnat : (6261171851 : ℕ)^71*50000000000000^55 ≤ 27319383890403^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6261171851 10000000000 27319383890403 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-864458459/10000000000 : ℝ), (5023793103/10000000000 : ℝ), (6261171851/10000000000 : ℝ)] ![(16565073379/390625000000 : ℝ), (41120573419851/100000000000000 : ℝ), (27319383890403/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-864458459/10000000000 : ℝ)|^71 ≤ (16565073379/390625000000 : ℝ)^55
        have hw : |(-864458459/10000000000 : ℝ)|=(864458459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5023793103/10000000000 : ℝ)|^71 ≤ (41120573419851/100000000000000 : ℝ)^55
        have hw : |(5023793103/10000000000 : ℝ)|=(5023793103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6261171851/10000000000 : ℝ)|^71 ≤ (27319383890403/50000000000000 : ℝ)^55
        have hw : |(6261171851/10000000000 : ℝ)|=(6261171851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310063_s4_s4_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4596766271/10000000000 : ℝ)*x 0 + (-303598051/2000000000 : ℝ)*x 1 + (6254417613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4596766271/10000000000 : ℝ)^71 ≤ (36665428338961/100000000000000 : ℝ)^55 := by
    have hnat : (4596766271 : ℕ)^71*100000000000000^55 ≤ 36665428338961^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4596766271 10000000000 36665428338961 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (303598051/2000000000 : ℝ)^71 ≤ (4385940060381/50000000000000 : ℝ)^55 := by
    have hnat : (303598051 : ℕ)^71*50000000000000^55 ≤ 4385940060381^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      303598051 2000000000 4385940060381 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6254417613/10000000000 : ℝ)^71 ≤ (13640672881513/25000000000000 : ℝ)^55 := by
    have hnat : (6254417613 : ℕ)^71*25000000000000^55 ≤ 13640672881513^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6254417613 10000000000 13640672881513 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4596766271/10000000000 : ℝ), (-303598051/2000000000 : ℝ), (6254417613/10000000000 : ℝ)] ![(36665428338961/100000000000000 : ℝ), (4385940060381/50000000000000 : ℝ), (13640672881513/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4596766271/10000000000 : ℝ)|^71 ≤ (36665428338961/100000000000000 : ℝ)^55
        have hw : |(4596766271/10000000000 : ℝ)|=(4596766271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-303598051/2000000000 : ℝ)|^71 ≤ (4385940060381/50000000000000 : ℝ)^55
        have hw : |(-303598051/2000000000 : ℝ)|=(303598051/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6254417613/10000000000 : ℝ)|^71 ≤ (13640672881513/25000000000000 : ℝ)^55
        have hw : |(6254417613/10000000000 : ℝ)|=(6254417613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310063_s4_s4_16 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6255385399/10000000000 : ℝ)*x 0 + (314898303/625000000 : ℝ)*x 1 + (-170075997/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6255385399/10000000000 : ℝ)^71 ≤ (1705424709449/3125000000000 : ℝ)^55 := by
    have hnat : (6255385399 : ℕ)^71*3125000000000^55 ≤ 1705424709449^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6255385399 10000000000 1705424709449 3125000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (314898303/625000000 : ℝ)^71 ≤ (41274692414897/100000000000000 : ℝ)^55 := by
    have hnat : (314898303 : ℕ)^71*100000000000000^55 ≤ 41274692414897^55*625000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314898303 625000000 41274692414897 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (170075997/2000000000 : ℝ)^71 ≤ (4151716876549/100000000000000 : ℝ)^55 := by
    have hnat : (170075997 : ℕ)^71*100000000000000^55 ≤ 4151716876549^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170075997 2000000000 4151716876549 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6255385399/10000000000 : ℝ), (314898303/625000000 : ℝ), (-170075997/2000000000 : ℝ)] ![(1705424709449/3125000000000 : ℝ), (41274692414897/100000000000000 : ℝ), (4151716876549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6255385399/10000000000 : ℝ)|^71 ≤ (1705424709449/3125000000000 : ℝ)^55
        have hw : |(6255385399/10000000000 : ℝ)|=(6255385399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(314898303/625000000 : ℝ)|^71 ≤ (41274692414897/100000000000000 : ℝ)^55
        have hw : |(314898303/625000000 : ℝ)|=(314898303/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-170075997/2000000000 : ℝ)|^71 ≤ (4151716876549/100000000000000 : ℝ)^55
        have hw : |(-170075997/2000000000 : ℝ)|=(170075997/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310063_s4_s4_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1540471519/2500000000 : ℝ)*x 0 + (786945221/2000000000 : ℝ)*x 1 + (2474167089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1540471519/2500000000 : ℝ)^71 ≤ (334517987449/625000000000 : ℝ)^55 := by
    have hnat : (1540471519 : ℕ)^71*625000000000^55 ≤ 334517987449^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1540471519 2500000000 334517987449 625000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (786945221/2000000000 : ℝ)^71 ≤ (14998280044049/50000000000000 : ℝ)^55 := by
    have hnat : (786945221 : ℕ)^71*50000000000000^55 ≤ 14998280044049^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      786945221 2000000000 14998280044049 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2474167089/10000000000 : ℝ)^71 ≤ (412014047701/2500000000000 : ℝ)^55 := by
    have hnat : (2474167089 : ℕ)^71*2500000000000^55 ≤ 412014047701^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2474167089 10000000000 412014047701 2500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1540471519/2500000000 : ℝ), (786945221/2000000000 : ℝ), (2474167089/10000000000 : ℝ)] ![(334517987449/625000000000 : ℝ), (14998280044049/50000000000000 : ℝ), (412014047701/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1540471519/2500000000 : ℝ)|^71 ≤ (334517987449/625000000000 : ℝ)^55
        have hw : |(1540471519/2500000000 : ℝ)|=(1540471519/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(786945221/2000000000 : ℝ)|^71 ≤ (14998280044049/50000000000000 : ℝ)^55
        have hw : |(786945221/2000000000 : ℝ)|=(786945221/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2474167089/10000000000 : ℝ)|^71 ≤ (412014047701/2500000000000 : ℝ)^55
        have hw : |(2474167089/10000000000 : ℝ)|=(2474167089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310063_s4_s4_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-403201697/5000000000 : ℝ)*x 0 + (118191147/200000000 : ℝ)*x 1 + (5425426061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (403201697/5000000000 : ℝ)^71 ≤ (3876666883223/100000000000000 : ℝ)^55 := by
    have hnat : (403201697 : ℕ)^71*100000000000000^55 ≤ 3876666883223^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403201697 5000000000 3876666883223 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (118191147/200000000 : ℝ)^71 ≤ (25355268546383/50000000000000 : ℝ)^55 := by
    have hnat : (118191147 : ℕ)^71*50000000000000^55 ≤ 25355268546383^55*200000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118191147 200000000 25355268546383 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5425426061/10000000000 : ℝ)^71 ≤ (9082559201559/20000000000000 : ℝ)^55 := by
    have hnat : (5425426061 : ℕ)^71*20000000000000^55 ≤ 9082559201559^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425426061 10000000000 9082559201559 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-403201697/5000000000 : ℝ), (118191147/200000000 : ℝ), (5425426061/10000000000 : ℝ)] ![(3876666883223/100000000000000 : ℝ), (25355268546383/50000000000000 : ℝ), (9082559201559/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-403201697/5000000000 : ℝ)|^71 ≤ (3876666883223/100000000000000 : ℝ)^55
        have hw : |(-403201697/5000000000 : ℝ)|=(403201697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(118191147/200000000 : ℝ)|^71 ≤ (25355268546383/50000000000000 : ℝ)^55
        have hw : |(118191147/200000000 : ℝ)|=(118191147/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5425426061/10000000000 : ℝ)|^71 ≤ (9082559201559/20000000000000 : ℝ)^55
        have hw : |(5425426061/10000000000 : ℝ)|=(5425426061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310063_s4_s4_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (629445687/1000000000 : ℝ)*x 0 + (-803985909/10000000000 : ℝ)*x 1 + (1004829301/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (629445687/1000000000 : ℝ)^71 ≤ (27507010751627/50000000000000 : ℝ)^55 := by
    have hnat : (629445687 : ℕ)^71*50000000000000^55 ≤ 27507010751627^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      629445687 1000000000 27507010751627 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (803985909/10000000000 : ℝ)^71 ≤ (1930835431219/50000000000000 : ℝ)^55 := by
    have hnat : (803985909 : ℕ)^71*50000000000000^55 ≤ 1930835431219^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      803985909 10000000000 1930835431219 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1004829301/2000000000 : ℝ)^71 ≤ (20562153805403/50000000000000 : ℝ)^55 := by
    have hnat : (1004829301 : ℕ)^71*50000000000000^55 ≤ 20562153805403^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004829301 2000000000 20562153805403 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(629445687/1000000000 : ℝ), (-803985909/10000000000 : ℝ), (1004829301/2000000000 : ℝ)] ![(27507010751627/50000000000000 : ℝ), (1930835431219/50000000000000 : ℝ), (20562153805403/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(629445687/1000000000 : ℝ)|^71 ≤ (27507010751627/50000000000000 : ℝ)^55
        have hw : |(629445687/1000000000 : ℝ)|=(629445687/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-803985909/10000000000 : ℝ)|^71 ≤ (1930835431219/50000000000000 : ℝ)^55
        have hw : |(-803985909/10000000000 : ℝ)|=(803985909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1004829301/2000000000 : ℝ)|^71 ≤ (20562153805403/50000000000000 : ℝ)^55
        have hw : |(1004829301/2000000000 : ℝ)|=(1004829301/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310063_s4_s4_23 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2271050831/5000000000 : ℝ)*x 0 + (6318660527/10000000000 : ℝ)*x 1 + (-1496137393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2271050831/5000000000 : ℝ)^71 ≤ (9025884277551/25000000000000 : ℝ)^55 := by
    have hnat : (2271050831 : ℕ)^71*25000000000000^55 ≤ 9025884277551^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2271050831 5000000000 9025884277551 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6318660527/10000000000 : ℝ)^71 ≤ (1727726727701/3125000000000 : ℝ)^55 := by
    have hnat : (6318660527 : ℕ)^71*3125000000000^55 ≤ 1727726727701^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6318660527 10000000000 1727726727701 3125000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1496137393/10000000000 : ℝ)^71 ≤ (4304603795307/50000000000000 : ℝ)^55 := by
    have hnat : (1496137393 : ℕ)^71*50000000000000^55 ≤ 4304603795307^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1496137393 10000000000 4304603795307 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2271050831/5000000000 : ℝ), (6318660527/10000000000 : ℝ), (-1496137393/10000000000 : ℝ)] ![(9025884277551/25000000000000 : ℝ), (1727726727701/3125000000000 : ℝ), (4304603795307/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2271050831/5000000000 : ℝ)|^71 ≤ (9025884277551/25000000000000 : ℝ)^55
        have hw : |(2271050831/5000000000 : ℝ)|=(2271050831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6318660527/10000000000 : ℝ)|^71 ≤ (1727726727701/3125000000000 : ℝ)^55
        have hw : |(6318660527/10000000000 : ℝ)|=(6318660527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1496137393/10000000000 : ℝ)|^71 ≤ (4304603795307/50000000000000 : ℝ)^55
        have hw : |(-1496137393/10000000000 : ℝ)|=(1496137393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310063_s4_s4_27 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6326566453/10000000000 : ℝ)*x 0 + (1610209327/5000000000 : ℝ)*x 1 + (94871243/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6326566453/10000000000 : ℝ)^71 ≤ (13844142726699/25000000000000 : ℝ)^55 := by
    have hnat : (6326566453 : ℕ)^71*25000000000000^55 ≤ 13844142726699^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6326566453 10000000000 13844142726699 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1610209327/5000000000 : ℝ)^71 ≤ (23161120064531/100000000000000 : ℝ)^55 := by
    have hnat : (1610209327 : ℕ)^71*100000000000000^55 ≤ 23161120064531^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1610209327 5000000000 23161120064531 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (94871243/312500000 : ℝ)^71 ≤ (10731154510463/50000000000000 : ℝ)^55 := by
    have hnat : (94871243 : ℕ)^71*50000000000000^55 ≤ 10731154510463^55*312500000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94871243 312500000 10731154510463 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6326566453/10000000000 : ℝ), (1610209327/5000000000 : ℝ), (94871243/312500000 : ℝ)] ![(13844142726699/25000000000000 : ℝ), (23161120064531/100000000000000 : ℝ), (10731154510463/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6326566453/10000000000 : ℝ)|^71 ≤ (13844142726699/25000000000000 : ℝ)^55
        have hw : |(6326566453/10000000000 : ℝ)|=(6326566453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1610209327/5000000000 : ℝ)|^71 ≤ (23161120064531/100000000000000 : ℝ)^55
        have hw : |(1610209327/5000000000 : ℝ)|=(1610209327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(94871243/312500000 : ℝ)|^71 ≤ (10731154510463/50000000000000 : ℝ)^55
        have hw : |(94871243/312500000 : ℝ)|=(94871243/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310063_s4 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev3 : (0 : ℝ) ≤ ((47069/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(47069/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(47853/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(47853/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22861/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(22861/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((34089/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(34089/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17269/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17269/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32999/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(32999/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
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
  have s4_pow0 : (47069/100000 : ℝ) ^ (35/8 : ℝ) ≤ (1850058687388622683/50000000000000000000 : ℝ) := by
    have hpowers : (47069/100000 : ℝ)^35 ≤ (1850058687388622683/50000000000000000000 : ℝ)^8 := by
      have hnat : (47069 : ℕ)^35*50000000000000000000^8 ≤ 1850058687388622683^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        47069 100000 1850058687388622683 50000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (47069/100000 : ℝ)) (X := (1850058687388622683/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s4_corner0a : (51850058687388622683/50000000000000000000 : ℝ) ≤ (10083392793602593/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (51850058687388622683/50000000000000000000 : ℝ)^8 ≤ (10083392793602593/10000000000000000 : ℝ)^35 := by
      have hnat : (51850058687388622683 : ℕ)^8*10000000000000000^35 ≤ 10083392793602593^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51850058687388622683 50000000000000000000 10083392793602593 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10083392793602593/10000000000000000 : ℝ)) (X := (51850058687388622683/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s4_corner0b : (26850058687388622683/25000000000000000000 : ℝ) ≤ (2541130205514549/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (26850058687388622683/25000000000000000000 : ℝ)^8 ≤ (2541130205514549/2500000000000000 : ℝ)^35 := by
      have hnat : (26850058687388622683 : ℕ)^8*2500000000000000^35 ≤ 2541130205514549^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26850058687388622683 25000000000000000000 2541130205514549 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2541130205514549/2500000000000000 : ℝ)) (X := (26850058687388622683/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s4_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(83392793602593/4706900000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(81128028455603/4706900000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (47069/100000 : ℝ)) (alpha := (83392793602593/4706900000000000 : ℝ)) (beta := (81128028455603/4706900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow0,s4_corner0a]) (by linarith only [s4_pow0,s4_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (47069/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(83392793602593/4706900000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(81128028455603/4706900000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow1 : (47853/100000 : ℝ) ^ (35/8 : ℝ) ≤ (1988715332294785233/50000000000000000000 : ℝ) := by
    have hpowers : (47853/100000 : ℝ)^35 ≤ (1988715332294785233/50000000000000000000 : ℝ)^8 := by
      have hnat : (47853 : ℕ)^35*50000000000000000000^8 ≤ 1988715332294785233^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        47853 100000 1988715332294785233 50000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (47853/100000 : ℝ)) (X := (1988715332294785233/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s4_corner1a : (51988715332294785233/50000000000000000000 : ℝ) ≤ (10089549842124933/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (51988715332294785233/50000000000000000000 : ℝ)^8 ≤ (10089549842124933/10000000000000000 : ℝ)^35 := by
      have hnat : (51988715332294785233 : ℕ)^8*10000000000000000^35 ≤ 10089549842124933^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51988715332294785233 50000000000000000000 10089549842124933 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10089549842124933/10000000000000000 : ℝ)) (X := (51988715332294785233/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s4_corner1b : (26988715332294785233/25000000000000000000 : ℝ) ≤ (10176494870560019/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (26988715332294785233/25000000000000000000 : ℝ)^8 ≤ (10176494870560019/10000000000000000 : ℝ)^35 := by
      have hnat : (26988715332294785233 : ℕ)^8*10000000000000000^35 ≤ 10176494870560019^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26988715332294785233 25000000000000000000 10176494870560019 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10176494870560019/10000000000000000 : ℝ)) (X := (26988715332294785233/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s4_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(89549842124933/4785300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(43472514217543/2392650000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (47853/100000 : ℝ)) (alpha := (89549842124933/4785300000000000 : ℝ)) (beta := (43472514217543/2392650000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow1,s4_corner1a]) (by linarith only [s4_pow1,s4_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (47853/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(89549842124933/4785300000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(43472514217543/2392650000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow2 : (22861/50000 : ℝ) ^ (35/8 : ℝ) ≤ (814681479049759453/25000000000000000000 : ℝ) := by
    have hpowers : (22861/50000 : ℝ)^35 ≤ (814681479049759453/25000000000000000000 : ℝ)^8 := by
      have hnat : (22861 : ℕ)^35*25000000000000000000^8 ≤ 814681479049759453^8*50000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22861 50000 814681479049759453 25000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22861/50000 : ℝ)) (X := (814681479049759453/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s4_corner2a : (25814681479049759453/25000000000000000000 : ℝ) ≤ (2014713310016109/2000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (25814681479049759453/25000000000000000000 : ℝ)^8 ≤ (2014713310016109/2000000000000000 : ℝ)^35 := by
      have hnat : (25814681479049759453 : ℕ)^8*2000000000000000^35 ≤ 2014713310016109^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25814681479049759453 25000000000000000000 2014713310016109 2000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2014713310016109/2000000000000000 : ℝ)) (X := (25814681479049759453/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s4_corner2b : (13314681479049759453/12500000000000000000 : ℝ) ≤ (5072681658424127/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (13314681479049759453/12500000000000000000 : ℝ)^8 ≤ (5072681658424127/5000000000000000 : ℝ)^35 := by
      have hnat : (13314681479049759453 : ℕ)^8*5000000000000000^35 ≤ 5072681658424127^35*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13314681479049759453 12500000000000000000 5072681658424127 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5072681658424127/5000000000000000 : ℝ)) (X := (13314681479049759453/12500000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s4_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(14713310016109/914440000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(71796766767709/4572200000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (22861/50000 : ℝ)) (alpha := (14713310016109/914440000000000 : ℝ)) (beta := (71796766767709/4572200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow2,s4_corner2a]) (by linarith only [s4_pow2,s4_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (22861/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(14713310016109/914440000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(71796766767709/4572200000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s4_0 : ((-1645710499/10000000000 : ℝ)*X 0 0+(336687969/625000000 : ℝ)*X 0 1+(541182049/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310063_s4_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_1 : ((5387965847/10000000000 : ℝ)*X 1 0+(-206725649/1250000000 : ℝ)*X 1 1+(2702566371/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310063_s4_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_2 : ((5406766497/10000000000 : ℝ)*X 2 0+(1350361603/2500000000 : ℝ)*X 2 1+(-408111151/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310063_s4_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_6 : ((171112921/400000000 : ℝ)*X 0 0+(4273707883/10000000000 : ℝ)*X 0 1+(1064402617/2500000000 : ℝ)*X 0 2+(171112921/400000000 : ℝ)*X 1 0+(4273707883/10000000000 : ℝ)*X 1 1+(1064402617/2500000000 : ℝ)*X 1 2+(171112921/400000000 : ℝ)*X 2 0+(4273707883/10000000000 : ℝ)*X 2 1+(1064402617/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310063_s4_s4_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_7 : ((-760403843/5000000000 : ℝ)*X 0 0+(915015097/2000000000 : ℝ)*X 0 1+(6272361949/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310063_s4_s4_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_8 : ((5014092143/10000000000 : ℝ)*X 1 0+(-872734803/10000000000 : ℝ)*X 1 1+(3132804491/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310063_s4_s4_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_9 : ((4803227149/10000000000 : ℝ)*X 2 0+(3239880199/5000000000 : ℝ)*X 2 1+(-419594931/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310063_s4_s4_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_13 : ((89546447/200000000 : ℝ)*X 0 0+(5690220907/10000000000 : ℝ)*X 0 1+(489828343/2000000000 : ℝ)*X 0 2+(89546447/200000000 : ℝ)*X 1 0+(5690220907/10000000000 : ℝ)*X 1 1+(489828343/2000000000 : ℝ)*X 1 2+(89546447/200000000 : ℝ)*X 2 0+(5690220907/10000000000 : ℝ)*X 2 1+(489828343/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310063_s4_s4_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_14 : ((-864458459/10000000000 : ℝ)*X 0 0+(5023793103/10000000000 : ℝ)*X 0 1+(6261171851/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310063_s4_s4_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_15 : ((4596766271/10000000000 : ℝ)*X 1 0+(-303598051/2000000000 : ℝ)*X 1 1+(6254417613/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310063_s4_s4_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_16 : ((6255385399/10000000000 : ℝ)*X 2 0+(314898303/625000000 : ℝ)*X 2 1+(-170075997/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310063_s4_s4_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_20 : ((1540471519/2500000000 : ℝ)*X 0 0+(786945221/2000000000 : ℝ)*X 0 1+(2474167089/10000000000 : ℝ)*X 0 2+(1540471519/2500000000 : ℝ)*X 1 0+(786945221/2000000000 : ℝ)*X 1 1+(2474167089/10000000000 : ℝ)*X 1 2+(1540471519/2500000000 : ℝ)*X 2 0+(786945221/2000000000 : ℝ)*X 2 1+(2474167089/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310063_s4_s4_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_21 : ((-403201697/5000000000 : ℝ)*X 0 0+(118191147/200000000 : ℝ)*X 0 1+(5425426061/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310063_s4_s4_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_22 : ((629445687/1000000000 : ℝ)*X 1 0+(-803985909/10000000000 : ℝ)*X 1 1+(1004829301/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310063_s4_s4_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_23 : ((2271050831/5000000000 : ℝ)*X 2 0+(6318660527/10000000000 : ℝ)*X 2 1+(-1496137393/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310063_s4_s4_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_27 : ((6326566453/10000000000 : ℝ)*X 0 0+(1610209327/5000000000 : ℝ)*X 0 1+(94871243/312500000 : ℝ)*X 0 2+(6326566453/10000000000 : ℝ)*X 1 0+(1610209327/5000000000 : ℝ)*X 1 1+(94871243/312500000 : ℝ)*X 1 2+(6326566453/10000000000 : ℝ)*X 2 0+(1610209327/5000000000 : ℝ)*X 2 1+(94871243/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310063_s4_s4_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s4_0 : (0 : ℝ) ≤ ((34089/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(34089/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (205215034970645975045105899/36465581100000000000000000000000 : ℝ) := by norm_num
    linear_combination (491021/500000000000 : ℝ)*(base50) + (138442824183/1000000000000 : ℝ)*(base60) + (4358533602671/1000000000000 : ℝ)*(major_s4_0) + (4358533602671/1000000000000 : ℝ)*(major_s4_1) + (4358533602671/1000000000000 : ℝ)*(major_s4_2) + (5790989/500000000000 : ℝ)*(sp_s4_0) + (6510933/1000000000000 : ℝ)*(sp_s4_6) + (376446464449/62500000000 : ℝ)*(sp_s4_7) + (188222942231/31250000000 : ℝ)*(sp_s4_8) + (6023135794931/1000000000000 : ℝ)*(sp_s4_9) + (16836803309/6250000000 : ℝ)*(sp_s4_13) + (190949/12500000000 : ℝ)*(sp_s4_14) + (36137691/1000000000000 : ℝ)*(sp_s4_15) + (34494151/1000000000000 : ℝ)*(sp_s4_23) + (2693895040373/1000000000000 : ℝ)*(f.failure) + (6023170289083/1000000000000 : ℝ)*(f.sum) + (40469206244837851541/218793486600000000000000000000000 : ℝ)*base63 + (2685493610340919/4572200000000000000000000000 : ℝ)*base65 + (1332199277442353/2392650000000000000000000000 : ℝ)*base67 + (205919152364091/914440000000000000000000000 : ℝ)*base69 + (9162595836509861883/215208881800000000000000000000000 : ℝ)*base70 + (636244263713623/4706900000000000000000000000 : ℝ)*base73 + (4063967503814863/4785300000000000000000000000 : ℝ)*base75 + (3519513564492443/4706900000000000000000000000 : ℝ)*base77 + (62865363475034262427/225239285700000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (31211/100000000000000000 : ℝ)*base86 + (31211/100000000000000000 : ℝ)*base88 + (31211/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s4_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17269/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17269/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (832431390979929656760802046387/114426562453060000000000000000000000 : ℝ) := by norm_num
    linear_combination (2008033/500000000000 : ℝ)*(base60) + (4413396943713/1000000000000 : ℝ)*(major_s4_0) + (4413396943713/1000000000000 : ℝ)*(major_s4_1) + (4413396943713/1000000000000 : ℝ)*(major_s4_2) + (2090037/31250000000 : ℝ)*(sp_s4_0) + (58428391/1000000000000 : ℝ)*(sp_s4_1) + (46628441/500000000000 : ℝ)*(sp_s4_2) + (3077453/250000000000 : ℝ)*(sp_s4_7) + (54908629/1000000000000 : ℝ)*(sp_s4_8) + (1524726910573/250000000000 : ℝ)*(sp_s4_14) + (3049436748133/500000000000 : ℝ)*(sp_s4_15) + (1219778715281/200000000000 : ℝ)*(sp_s4_16) + (545541166723/200000000000 : ℝ)*(sp_s4_20) + (98795579/1000000000000 : ℝ)*(sp_s4_27) + (545560925839/200000000000 : ℝ)*(f.failure) + (6098986833287/1000000000000 : ℝ)*(f.sum) + (45256961232871882561/72931162200000000000000000000000 : ℝ)*base63 + (1190034182689543/4572200000000000000000000000 : ℝ)*base64 + (32628077993449/99693750000000000000000000 : ℝ)*base66 + (989065420184489/914440000000000000000000000 : ℝ)*base69 + (5841556142102103411/215208881800000000000000000000000 : ℝ)*base71 + (4043411167395009/4706900000000000000000000000 : ℝ)*base73 + (812047301136983/1595100000000000000000000000 : ℝ)*base75 + (1485828745042959/4706900000000000000000000000 : ℝ)*base77 + (13983072623933482963/75079761900000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base82 + (9327/20000000000000000 : ℝ)*base87 + (9327/20000000000000000 : ℝ)*base89 + (9327/20000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s4_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32999/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(32999/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (35452568841430084246217116419/4577062498122400000000000000000000 : ℝ) := by norm_num
    linear_combination (4962639/1000000000000 : ℝ)*(base15) + (13920602109/62500000000 : ℝ)*(base40) + (4085217663129/1000000000000 : ℝ)*(major_s4_0) + (4085217663129/1000000000000 : ℝ)*(major_s4_1) + (4085217663129/1000000000000 : ℝ)*(major_s4_2) + (2403451/62500000000 : ℝ)*(sp_s4_0) + (1560567/40000000000 : ℝ)*(sp_s4_1) + (21595397/1000000000000 : ℝ)*(sp_s4_2) + (4709243/200000000000 : ℝ)*(sp_s4_9) + (10085089/200000000000 : ℝ)*(sp_s4_20) + (5645428645919/1000000000000 : ℝ)*(sp_s4_21) + (5645423124321/1000000000000 : ℝ)*(sp_s4_22) + (5645421959523/1000000000000 : ℝ)*(sp_s4_23) + (2524915217771/1000000000000 : ℝ)*(sp_s4_27) + (157810352701/62500000000 : ℝ)*(f.failure) + (1129093420227/200000000000 : ℝ)*(f.sum) + (1995036697382265371/24310387400000000000000000000000 : ℝ)*base63 + (2012236417696401/4572200000000000000000000000 : ℝ)*base65 + (104430886352783/265850000000000000000000000 : ℝ)*base67 + (255848707626429/914440000000000000000000000 : ℝ)*base69 + (50206963362470484957/215208881800000000000000000000000 : ℝ)*base70 + (3826691194291147/4706900000000000000000000000 : ℝ)*base73 + (228903647228363/531700000000000000000000000 : ℝ)*base75 + (858962109010837/4706900000000000000000000000 : ℝ)*base77 + (7659307986214581413/25026587300000000000000000000000 : ℝ)*base79 + (3357/6250000000000000 : ℝ)*base86 + (3357/6250000000000000 : ℝ)*base88 + (3357/6250000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev3 : (0 : ℝ) ≤ ((47069/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(47069/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(47853/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(47853/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22861/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(22861/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((34089/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(34089/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17269/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17269/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32999/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(32999/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c310063_s4 p hpa hpb X hX hprev3

#print axioms solution

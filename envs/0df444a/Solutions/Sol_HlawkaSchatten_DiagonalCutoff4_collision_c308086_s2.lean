-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c308086_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:40:31.06399+00:00
-- url     : https://prove2.me/submissions/6ec9347d-575e-45ce-88a0-c187beb88f8b

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
theorem collision_support_c308086_s2_s2_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1200316651/2000000000 : ℝ)*x 0 + (-1738268757/5000000000 : ℝ)*x 1 + (-1632381183/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1200316651/2000000000 : ℝ)^69 ≤ (25721555190769/50000000000000 : ℝ)^53 := by
    have hnat : (1200316651 : ℕ)^69*50000000000000^53 ≤ 25721555190769^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1200316651 2000000000 25721555190769 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1738268757/5000000000 : ℝ)^69 ≤ (6317790845549/25000000000000 : ℝ)^53 := by
    have hnat : (1738268757 : ℕ)^69*25000000000000^53 ≤ 6317790845549^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1738268757 5000000000 6317790845549 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1632381183/5000000000 : ℝ)^69 ≤ (23285726222579/100000000000000 : ℝ)^53 := by
    have hnat : (1632381183 : ℕ)^69*100000000000000^53 ≤ 23285726222579^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1632381183 5000000000 23285726222579 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1200316651/2000000000 : ℝ), (-1738268757/5000000000 : ℝ), (-1632381183/5000000000 : ℝ)] ![(25721555190769/50000000000000 : ℝ), (6317790845549/25000000000000 : ℝ), (23285726222579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1200316651/2000000000 : ℝ)|^69 ≤ (25721555190769/50000000000000 : ℝ)^53
        have hw : |(1200316651/2000000000 : ℝ)|=(1200316651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1738268757/5000000000 : ℝ)|^69 ≤ (6317790845549/25000000000000 : ℝ)^53
        have hw : |(-1738268757/5000000000 : ℝ)|=(1738268757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1632381183/5000000000 : ℝ)|^69 ≤ (23285726222579/100000000000000 : ℝ)^53
        have hw : |(-1632381183/5000000000 : ℝ)|=(1632381183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s2_s2_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2000503163/5000000000 : ℝ)*x 0 + (-1459611803/5000000000 : ℝ)*x 1 + (5829076841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2000503163/5000000000 : ℝ)^69 ≤ (3792969918467/12500000000000 : ℝ)^53 := by
    have hnat : (2000503163 : ℕ)^69*12500000000000^53 ≤ 3792969918467^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000503163 5000000000 3792969918467 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1459611803/5000000000 : ℝ)^69 ≤ (20129762059691/100000000000000 : ℝ)^53 := by
    have hnat : (1459611803 : ℕ)^69*100000000000000^53 ≤ 20129762059691^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1459611803 5000000000 20129762059691 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5829076841/10000000000 : ℝ)^69 ≤ (3095404910949/6250000000000 : ℝ)^53 := by
    have hnat : (5829076841 : ℕ)^69*6250000000000^53 ≤ 3095404910949^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5829076841 10000000000 3095404910949 6250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2000503163/5000000000 : ℝ), (-1459611803/5000000000 : ℝ), (5829076841/10000000000 : ℝ)] ![(3792969918467/12500000000000 : ℝ), (20129762059691/100000000000000 : ℝ), (3095404910949/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2000503163/5000000000 : ℝ)|^69 ≤ (3792969918467/12500000000000 : ℝ)^53
        have hw : |(2000503163/5000000000 : ℝ)|=(2000503163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1459611803/5000000000 : ℝ)|^69 ≤ (20129762059691/100000000000000 : ℝ)^53
        have hw : |(-1459611803/5000000000 : ℝ)|=(1459611803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5829076841/10000000000 : ℝ)|^69 ≤ (3095404910949/6250000000000 : ℝ)^53
        have hw : |(5829076841/10000000000 : ℝ)|=(5829076841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s2_s2_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7239/250000000 : ℝ)*x 0 + (-969513197/1250000000 : ℝ)*x 1 + (755712309/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7239/250000000 : ℝ)^69 ≤ (30877163/25000000000000 : ℝ)^53 := by
    have hnat : (7239 : ℕ)^69*25000000000000^53 ≤ 30877163^53*250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7239 250000000 30877163 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (969513197/1250000000 : ℝ)^69 ≤ (7183376114553/10000000000000 : ℝ)^53 := by
    have hnat : (969513197 : ℕ)^69*10000000000000^53 ≤ 7183376114553^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      969513197 1250000000 7183376114553 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (755712309/2000000000 : ℝ)^69 ≤ (28166115335753/100000000000000 : ℝ)^53 := by
    have hnat : (755712309 : ℕ)^69*100000000000000^53 ≤ 28166115335753^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      755712309 2000000000 28166115335753 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7239/250000000 : ℝ), (-969513197/1250000000 : ℝ), (755712309/2000000000 : ℝ)] ![(30877163/25000000000000 : ℝ), (7183376114553/10000000000000 : ℝ), (28166115335753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7239/250000000 : ℝ)|^69 ≤ (30877163/25000000000000 : ℝ)^53
        have hw : |(7239/250000000 : ℝ)|=(7239/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-969513197/1250000000 : ℝ)|^69 ≤ (7183376114553/10000000000000 : ℝ)^53
        have hw : |(-969513197/1250000000 : ℝ)|=(969513197/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(755712309/2000000000 : ℝ)|^69 ≤ (28166115335753/100000000000000 : ℝ)^53
        have hw : |(755712309/2000000000 : ℝ)|=(755712309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s2_s2_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2908265511/5000000000 : ℝ)*x 0 + (1804811913/5000000000 : ℝ)*x 1 + (1674684773/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2908265511/5000000000 : ℝ)^69 ≤ (49387749106121/100000000000000 : ℝ)^53 := by
    have hnat : (2908265511 : ℕ)^69*100000000000000^53 ≤ 49387749106121^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2908265511 5000000000 49387749106121 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1804811913/5000000000 : ℝ)^69 ≤ (26537838728821/100000000000000 : ℝ)^53 := by
    have hnat : (1804811913 : ℕ)^69*100000000000000^53 ≤ 26537838728821^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1804811913 5000000000 26537838728821 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1674684773/5000000000 : ℝ)^69 ≤ (4814882429471/20000000000000 : ℝ)^53 := by
    have hnat : (1674684773 : ℕ)^69*20000000000000^53 ≤ 4814882429471^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1674684773 5000000000 4814882429471 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2908265511/5000000000 : ℝ), (1804811913/5000000000 : ℝ), (1674684773/5000000000 : ℝ)] ![(49387749106121/100000000000000 : ℝ), (26537838728821/100000000000000 : ℝ), (4814882429471/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2908265511/5000000000 : ℝ)|^69 ≤ (49387749106121/100000000000000 : ℝ)^53
        have hw : |(2908265511/5000000000 : ℝ)|=(2908265511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1804811913/5000000000 : ℝ)|^69 ≤ (26537838728821/100000000000000 : ℝ)^53
        have hw : |(1804811913/5000000000 : ℝ)|=(1804811913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1674684773/5000000000 : ℝ)|^69 ≤ (4814882429471/20000000000000 : ℝ)^53
        have hw : |(1674684773/5000000000 : ℝ)|=(1674684773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s2_s2_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (225581513/400000000 : ℝ)*x 0 + (-445531197/1250000000 : ℝ)*x 1 + (-3601002937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (225581513/400000000 : ℝ)^69 ≤ (11860069249651/25000000000000 : ℝ)^53 := by
    have hnat : (225581513 : ℕ)^69*25000000000000^53 ≤ 11860069249651^53*400000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225581513 400000000 11860069249651 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (445531197/1250000000 : ℝ)^69 ≤ (6526092183573/25000000000000 : ℝ)^53 := by
    have hnat : (445531197 : ℕ)^69*25000000000000^53 ≤ 6526092183573^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445531197 1250000000 6526092183573 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3601002937/10000000000 : ℝ)^69 ≤ (6613838564041/25000000000000 : ℝ)^53 := by
    have hnat : (3601002937 : ℕ)^69*25000000000000^53 ≤ 6613838564041^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3601002937 10000000000 6613838564041 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(225581513/400000000 : ℝ), (-445531197/1250000000 : ℝ), (-3601002937/10000000000 : ℝ)] ![(11860069249651/25000000000000 : ℝ), (6526092183573/25000000000000 : ℝ), (6613838564041/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(225581513/400000000 : ℝ)|^69 ≤ (11860069249651/25000000000000 : ℝ)^53
        have hw : |(225581513/400000000 : ℝ)|=(225581513/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-445531197/1250000000 : ℝ)|^69 ≤ (6526092183573/25000000000000 : ℝ)^53
        have hw : |(-445531197/1250000000 : ℝ)|=(445531197/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3601002937/10000000000 : ℝ)|^69 ≤ (6613838564041/25000000000000 : ℝ)^53
        have hw : |(-3601002937/10000000000 : ℝ)|=(3601002937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s2_s2_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (257256269/1000000000 : ℝ)*x 0 + (-322144823/2500000000 : ℝ)*x 1 + (8097991211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (257256269/1000000000 : ℝ)^69 ≤ (8537549684243/50000000000000 : ℝ)^53 := by
    have hnat : (257256269 : ℕ)^69*50000000000000^53 ≤ 8537549684243^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257256269 1000000000 8537549684243 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (322144823/2500000000 : ℝ)^69 ≤ (3470846928989/50000000000000 : ℝ)^53 := by
    have hnat : (322144823 : ℕ)^69*50000000000000^53 ≤ 3470846928989^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322144823 2500000000 3470846928989 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8097991211/10000000000 : ℝ)^69 ≤ (37991603381589/50000000000000 : ℝ)^53 := by
    have hnat : (8097991211 : ℕ)^69*50000000000000^53 ≤ 37991603381589^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8097991211 10000000000 37991603381589 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(257256269/1000000000 : ℝ), (-322144823/2500000000 : ℝ), (8097991211/10000000000 : ℝ)] ![(8537549684243/50000000000000 : ℝ), (3470846928989/50000000000000 : ℝ), (37991603381589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(257256269/1000000000 : ℝ)|^69 ≤ (8537549684243/50000000000000 : ℝ)^53
        have hw : |(257256269/1000000000 : ℝ)|=(257256269/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-322144823/2500000000 : ℝ)|^69 ≤ (3470846928989/50000000000000 : ℝ)^53
        have hw : |(-322144823/2500000000 : ℝ)|=(322144823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8097991211/10000000000 : ℝ)|^69 ≤ (37991603381589/50000000000000 : ℝ)^53
        have hw : |(8097991211/10000000000 : ℝ)|=(8097991211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s2_s2_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-10733/5000000000 : ℝ)*x 0 + (-2397537493/5000000000 : ℝ)*x 1 + (3445842541/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10733/5000000000 : ℝ)^69 ≤ (4174281/100000000000000 : ℝ)^53 := by
    have hnat : (10733 : ℕ)^69*100000000000000^53 ≤ 4174281^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10733 5000000000 4174281 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2397537493/5000000000 : ℝ)^69 ≤ (4801111192459/12500000000000 : ℝ)^53 := by
    have hnat : (2397537493 : ℕ)^69*12500000000000^53 ≤ 4801111192459^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2397537493 5000000000 4801111192459 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3445842541/5000000000 : ℝ)^69 ≤ (61591106279257/100000000000000 : ℝ)^53 := by
    have hnat : (3445842541 : ℕ)^69*100000000000000^53 ≤ 61591106279257^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3445842541 5000000000 61591106279257 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-10733/5000000000 : ℝ), (-2397537493/5000000000 : ℝ), (3445842541/5000000000 : ℝ)] ![(4174281/100000000000000 : ℝ), (4801111192459/12500000000000 : ℝ), (61591106279257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-10733/5000000000 : ℝ)|^69 ≤ (4174281/100000000000000 : ℝ)^53
        have hw : |(-10733/5000000000 : ℝ)|=(10733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2397537493/5000000000 : ℝ)|^69 ≤ (4801111192459/12500000000000 : ℝ)^53
        have hw : |(-2397537493/5000000000 : ℝ)|=(2397537493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3445842541/5000000000 : ℝ)|^69 ≤ (61591106279257/100000000000000 : ℝ)^53
        have hw : |(3445842541/5000000000 : ℝ)|=(3445842541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s2_s2_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7869551567/10000000000 : ℝ)*x 0 + (300356791/1250000000 : ℝ)*x 1 + (1857166873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7869551567/10000000000 : ℝ)^69 ≤ (73204648626057/100000000000000 : ℝ)^53 := by
    have hnat : (7869551567 : ℕ)^69*100000000000000^53 ≤ 73204648626057^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7869551567 10000000000 73204648626057 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (300356791/1250000000 : ℝ)^69 ≤ (7811730303337/50000000000000 : ℝ)^53 := by
    have hnat : (300356791 : ℕ)^69*50000000000000^53 ≤ 7811730303337^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300356791 1250000000 7811730303337 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1857166873/10000000000 : ℝ)^69 ≤ (11171890756947/100000000000000 : ℝ)^53 := by
    have hnat : (1857166873 : ℕ)^69*100000000000000^53 ≤ 11171890756947^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1857166873 10000000000 11171890756947 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7869551567/10000000000 : ℝ), (300356791/1250000000 : ℝ), (1857166873/10000000000 : ℝ)] ![(73204648626057/100000000000000 : ℝ), (7811730303337/50000000000000 : ℝ), (11171890756947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7869551567/10000000000 : ℝ)|^69 ≤ (73204648626057/100000000000000 : ℝ)^53
        have hw : |(7869551567/10000000000 : ℝ)|=(7869551567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(300356791/1250000000 : ℝ)|^69 ≤ (7811730303337/50000000000000 : ℝ)^53
        have hw : |(300356791/1250000000 : ℝ)|=(300356791/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1857166873/10000000000 : ℝ)|^69 ≤ (11171890756947/100000000000000 : ℝ)^53
        have hw : |(1857166873/10000000000 : ℝ)|=(1857166873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s2_s2_16 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3683705181/5000000000 : ℝ)*x 0 + (-3022499399/10000000000 : ℝ)*x 1 + (-482803599/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3683705181/5000000000 : ℝ)^69 ≤ (67182934475819/100000000000000 : ℝ)^53 := by
    have hnat : (3683705181 : ℕ)^69*100000000000000^53 ≤ 67182934475819^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3683705181 5000000000 67182934475819 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3022499399/10000000000 : ℝ)^69 ≤ (1053090399107/5000000000000 : ℝ)^53 := by
    have hnat : (3022499399 : ℕ)^69*5000000000000^53 ≤ 1053090399107^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3022499399 10000000000 1053090399107 5000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (482803599/2500000000 : ℝ)^69 ≤ (587762876003/5000000000000 : ℝ)^53 := by
    have hnat : (482803599 : ℕ)^69*5000000000000^53 ≤ 587762876003^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482803599 2500000000 587762876003 5000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3683705181/5000000000 : ℝ), (-3022499399/10000000000 : ℝ), (-482803599/2500000000 : ℝ)] ![(67182934475819/100000000000000 : ℝ), (1053090399107/5000000000000 : ℝ), (587762876003/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3683705181/5000000000 : ℝ)|^69 ≤ (67182934475819/100000000000000 : ℝ)^53
        have hw : |(3683705181/5000000000 : ℝ)|=(3683705181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3022499399/10000000000 : ℝ)|^69 ≤ (1053090399107/5000000000000 : ℝ)^53
        have hw : |(-3022499399/10000000000 : ℝ)|=(3022499399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-482803599/2500000000 : ℝ)|^69 ≤ (587762876003/5000000000000 : ℝ)^53
        have hw : |(-482803599/2500000000 : ℝ)|=(482803599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s2_s2_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (76341361/312500000 : ℝ)*x 0 + (-1820016107/10000000000 : ℝ)*x 1 + (1966356327/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (76341361/312500000 : ℝ)^69 ≤ (159634939669/1000000000000 : ℝ)^53 := by
    have hnat : (76341361 : ℕ)^69*1000000000000^53 ≤ 159634939669^53*312500000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76341361 312500000 159634939669 1000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1820016107/10000000000 : ℝ)^69 ≤ (10881824475951/100000000000000 : ℝ)^53 := by
    have hnat : (1820016107 : ℕ)^69*100000000000000^53 ≤ 10881824475951^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1820016107 10000000000 10881824475951 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1966356327/2500000000 : ℝ)^69 ≤ (18288670385583/25000000000000 : ℝ)^53 := by
    have hnat : (1966356327 : ℕ)^69*25000000000000^53 ≤ 18288670385583^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1966356327 2500000000 18288670385583 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(76341361/312500000 : ℝ), (-1820016107/10000000000 : ℝ), (1966356327/2500000000 : ℝ)] ![(159634939669/1000000000000 : ℝ), (10881824475951/100000000000000 : ℝ), (18288670385583/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(76341361/312500000 : ℝ)|^69 ≤ (159634939669/1000000000000 : ℝ)^53
        have hw : |(76341361/312500000 : ℝ)|=(76341361/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1820016107/10000000000 : ℝ)|^69 ≤ (10881824475951/100000000000000 : ℝ)^53
        have hw : |(-1820016107/10000000000 : ℝ)|=(1820016107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1966356327/2500000000 : ℝ)|^69 ≤ (18288670385583/25000000000000 : ℝ)^53
        have hw : |(1966356327/2500000000 : ℝ)|=(1966356327/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s2_s2_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (41335777/10000000000 : ℝ)*x 0 + (-7575417659/10000000000 : ℝ)*x 1 + (1996176507/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41335777/10000000000 : ℝ)^69 ≤ (39418168687/50000000000000 : ℝ)^53 := by
    have hnat : (41335777 : ℕ)^69*50000000000000^53 ≤ 39418168687^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41335777 10000000000 39418168687 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7575417659/10000000000 : ℝ)^69 ≤ (34831407659299/50000000000000 : ℝ)^53 := by
    have hnat : (7575417659 : ℕ)^69*50000000000000^53 ≤ 34831407659299^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7575417659 10000000000 34831407659299 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1996176507/5000000000 : ℝ)^69 ≤ (30258348337693/100000000000000 : ℝ)^53 := by
    have hnat : (1996176507 : ℕ)^69*100000000000000^53 ≤ 30258348337693^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1996176507 5000000000 30258348337693 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41335777/10000000000 : ℝ), (-7575417659/10000000000 : ℝ), (1996176507/5000000000 : ℝ)] ![(39418168687/50000000000000 : ℝ), (34831407659299/50000000000000 : ℝ), (30258348337693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41335777/10000000000 : ℝ)|^69 ≤ (39418168687/50000000000000 : ℝ)^53
        have hw : |(41335777/10000000000 : ℝ)|=(41335777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7575417659/10000000000 : ℝ)|^69 ≤ (34831407659299/50000000000000 : ℝ)^53
        have hw : |(-7575417659/10000000000 : ℝ)|=(7575417659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1996176507/5000000000 : ℝ)|^69 ≤ (30258348337693/100000000000000 : ℝ)^53
        have hw : |(1996176507/5000000000 : ℝ)|=(1996176507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s2_s2_22 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1880133221/2500000000 : ℝ)*x 0 + (2628562807/10000000000 : ℝ)*x 1 + (1069805521/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1880133221/2500000000 : ℝ)^69 ≤ (17251613288081/25000000000000 : ℝ)^53 := by
    have hnat : (1880133221 : ℕ)^69*25000000000000^53 ≤ 17251613288081^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1880133221 2500000000 17251613288081 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2628562807/10000000000 : ℝ)^69 ≤ (3512117125351/20000000000000 : ℝ)^53 := by
    have hnat : (2628562807 : ℕ)^69*20000000000000^53 ≤ 3512117125351^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628562807 10000000000 3512117125351 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1069805521/5000000000 : ℝ)^69 ≤ (1679120150593/12500000000000 : ℝ)^53 := by
    have hnat : (1069805521 : ℕ)^69*12500000000000^53 ≤ 1679120150593^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069805521 5000000000 1679120150593 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1880133221/2500000000 : ℝ), (2628562807/10000000000 : ℝ), (1069805521/5000000000 : ℝ)] ![(17251613288081/25000000000000 : ℝ), (3512117125351/20000000000000 : ℝ), (1679120150593/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1880133221/2500000000 : ℝ)|^69 ≤ (17251613288081/25000000000000 : ℝ)^53
        have hw : |(1880133221/2500000000 : ℝ)|=(1880133221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2628562807/10000000000 : ℝ)|^69 ≤ (3512117125351/20000000000000 : ℝ)^53
        have hw : |(2628562807/10000000000 : ℝ)|=(2628562807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1069805521/5000000000 : ℝ)|^69 ≤ (1679120150593/12500000000000 : ℝ)^53
        have hw : |(1069805521/5000000000 : ℝ)|=(1069805521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s2_s2_23 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1165896139/2500000000 : ℝ)*x 0 + (-4867987779/10000000000 : ℝ)*x 1 + (-3318465717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1165896139/2500000000 : ℝ)^69 ≤ (1481735706371/4000000000000 : ℝ)^53 := by
    have hnat : (1165896139 : ℕ)^69*4000000000000^53 ≤ 1481735706371^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1165896139 2500000000 1481735706371 4000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4867987779/10000000000 : ℝ)^69 ≤ (3917097813471/10000000000000 : ℝ)^53 := by
    have hnat : (4867987779 : ℕ)^69*10000000000000^53 ≤ 3917097813471^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4867987779 10000000000 3917097813471 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3318465717/10000000000 : ℝ)^69 ≤ (23785629189653/100000000000000 : ℝ)^53 := by
    have hnat : (3318465717 : ℕ)^69*100000000000000^53 ≤ 23785629189653^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3318465717 10000000000 23785629189653 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1165896139/2500000000 : ℝ), (-4867987779/10000000000 : ℝ), (-3318465717/10000000000 : ℝ)] ![(1481735706371/4000000000000 : ℝ), (3917097813471/10000000000000 : ℝ), (23785629189653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1165896139/2500000000 : ℝ)|^69 ≤ (1481735706371/4000000000000 : ℝ)^53
        have hw : |(1165896139/2500000000 : ℝ)|=(1165896139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4867987779/10000000000 : ℝ)|^69 ≤ (3917097813471/10000000000000 : ℝ)^53
        have hw : |(-4867987779/10000000000 : ℝ)|=(4867987779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3318465717/10000000000 : ℝ)|^69 ≤ (23785629189653/100000000000000 : ℝ)^53
        have hw : |(-3318465717/10000000000 : ℝ)|=(3318465717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s2_s2_27 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1194967711/2000000000 : ℝ)*x 0 + (-1894762039/10000000000 : ℝ)*x 1 + (1174216409/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1194967711/2000000000 : ℝ)^69 ≤ (25572430412041/50000000000000 : ℝ)^53 := by
    have hnat : (1194967711 : ℕ)^69*50000000000000^53 ≤ 25572430412041^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1194967711 2000000000 25572430412041 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1894762039/10000000000 : ℝ)^69 ≤ (11467215478769/100000000000000 : ℝ)^53 := by
    have hnat : (1894762039 : ℕ)^69*100000000000000^53 ≤ 11467215478769^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1894762039 10000000000 11467215478769 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1174216409/2500000000 : ℝ)^69 ≤ (18693961837083/50000000000000 : ℝ)^53 := by
    have hnat : (1174216409 : ℕ)^69*50000000000000^53 ≤ 18693961837083^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1174216409 2500000000 18693961837083 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1194967711/2000000000 : ℝ), (-1894762039/10000000000 : ℝ), (1174216409/2500000000 : ℝ)] ![(25572430412041/50000000000000 : ℝ), (11467215478769/100000000000000 : ℝ), (18693961837083/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1194967711/2000000000 : ℝ)|^69 ≤ (25572430412041/50000000000000 : ℝ)^53
        have hw : |(1194967711/2000000000 : ℝ)|=(1194967711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1894762039/10000000000 : ℝ)|^69 ≤ (11467215478769/100000000000000 : ℝ)^53
        have hw : |(-1894762039/10000000000 : ℝ)|=(1894762039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1174216409/2500000000 : ℝ)|^69 ≤ (18693961837083/50000000000000 : ℝ)^53
        have hw : |(1174216409/2500000000 : ℝ)|=(1174216409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308086_s2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((35467/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(35467/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-16891/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-16891/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(83413/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(83413/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2277/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2277/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1797/2500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-1797/2500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1351/2000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1351/2000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (3861/5000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (3861/5000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (11517/6250 : ℝ) := by
    linarith only [f.Tcap]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s2_pow0 : (35467/50000 : ℝ) ^ (17/4 : ℝ) ≤ (23234397496854850079/100000000000000000000 : ℝ) := by
    have hpowers : (35467/50000 : ℝ)^17 ≤ (23234397496854850079/100000000000000000000 : ℝ)^4 := by
      have hnat : (35467 : ℕ)^17*100000000000000000000^4 ≤ 23234397496854850079^4*50000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35467 50000 23234397496854850079 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (35467/50000 : ℝ)) (X := (23234397496854850079/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner0a : (123234397496854850079/100000000000000000000 : ℝ) ≤ (1312981800270503/1250000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (123234397496854850079/100000000000000000000 : ℝ)^4 ≤ (1312981800270503/1250000000000000 : ℝ)^17 := by
      have hnat : (123234397496854850079 : ℕ)^4*1250000000000000^17 ≤ 1312981800270503^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        123234397496854850079 100000000000000000000 1312981800270503 1250000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1312981800270503/1250000000000000 : ℝ)) (X := (123234397496854850079/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner0b : (73234397496854850079/50000000000000000000 : ℝ) ≤ (5469767336021403/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (73234397496854850079/50000000000000000000 : ℝ)^4 ≤ (5469767336021403/5000000000000000 : ℝ)^17 := by
      have hnat : (73234397496854850079 : ℕ)^4*5000000000000000^17 ≤ 5469767336021403^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        73234397496854850079 50000000000000000000 5469767336021403 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5469767336021403/5000000000000000 : ℝ)) (X := (73234397496854850079/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(62981800270503/886675000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(217840134939391/3546700000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (35467/50000 : ℝ)) (alpha := (62981800270503/886675000000000 : ℝ)) (beta := (217840134939391/3546700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (35467/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(62981800270503/886675000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(217840134939391/3546700000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (16891/20000 : ℝ) ^ (17/4 : ℝ) ≤ (48770567216884850659/100000000000000000000 : ℝ) := by
    have hpowers : (16891/20000 : ℝ)^17 ≤ (48770567216884850659/100000000000000000000 : ℝ)^4 := by
      have hnat : (16891 : ℕ)^17*100000000000000000000^4 ≤ 48770567216884850659^4*20000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16891 20000 48770567216884850659 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16891/20000 : ℝ)) (X := (48770567216884850659/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner1a : (148770567216884850659/100000000000000000000 : ℝ) ≤ (439189785645693/400000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (148770567216884850659/100000000000000000000 : ℝ)^4 ≤ (439189785645693/400000000000000 : ℝ)^17 := by
      have hnat : (148770567216884850659 : ℕ)^4*400000000000000^17 ≤ 439189785645693^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        148770567216884850659 100000000000000000000 439189785645693 400000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (439189785645693/400000000000000 : ℝ)) (X := (148770567216884850659/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner1b : (98770567216884850659/50000000000000000000 : ℝ) ≤ (2347450679948713/2000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (98770567216884850659/50000000000000000000 : ℝ)^4 ≤ (2347450679948713/2000000000000000 : ℝ)^17 := by
      have hnat : (98770567216884850659 : ℕ)^4*2000000000000000^17 ≤ 2347450679948713^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        98770567216884850659 50000000000000000000 2347450679948713 2000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2347450679948713/2000000000000000 : ℝ)) (X := (98770567216884850659/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(39189785645693/337820000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(18937718965031/211137500000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (16891/20000 : ℝ)) (alpha := (39189785645693/337820000000000 : ℝ)) (beta := (18937718965031/211137500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (16891/20000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(39189785645693/337820000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(18937718965031/211137500000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (83413/100000 : ℝ) ^ (17/4 : ℝ) ≤ (23132011748300590827/50000000000000000000 : ℝ) := by
    have hpowers : (83413/100000 : ℝ)^17 ≤ (23132011748300590827/50000000000000000000 : ℝ)^4 := by
      have hnat : (83413 : ℕ)^17*50000000000000000000^4 ≤ 23132011748300590827^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        83413 100000 23132011748300590827 50000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (83413/100000 : ℝ)) (X := (23132011748300590827/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner2a : (73132011748300590827/50000000000000000000 : ℝ) ≤ (10935934140688151/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (73132011748300590827/50000000000000000000 : ℝ)^4 ≤ (10935934140688151/10000000000000000 : ℝ)^17 := by
      have hnat : (73132011748300590827 : ℕ)^4*10000000000000000^17 ≤ 10935934140688151^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        73132011748300590827 50000000000000000000 10935934140688151 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10935934140688151/10000000000000000 : ℝ)) (X := (73132011748300590827/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner2b : (48132011748300590827/25000000000000000000 : ℝ) ≤ (11666477988070053/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (48132011748300590827/25000000000000000000 : ℝ)^4 ≤ (11666477988070053/10000000000000000 : ℝ)^17 := by
      have hnat : (48132011748300590827 : ℕ)^4*10000000000000000^17 ≤ 11666477988070053^17*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        48132011748300590827 25000000000000000000 11666477988070053 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11666477988070053/10000000000000000 : ℝ)) (X := (48132011748300590827/25000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(85084921880741/758300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(365271923690951/4170650000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (83413/100000 : ℝ)) (alpha := (85084921880741/758300000000000 : ℝ)) (beta := (365271923690951/4170650000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (83413/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(85084921880741/758300000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(365271923690951/4170650000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_2 : ((1200316651/2000000000 : ℝ)*X 2 0+(-1738268757/5000000000 : ℝ)*X 2 1+(-1632381183/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((2000503163/5000000000 : ℝ)*X 0 0+(-1459611803/5000000000 : ℝ)*X 0 1+(5829076841/10000000000 : ℝ)*X 0 2+(2000503163/5000000000 : ℝ)*X 1 0+(-1459611803/5000000000 : ℝ)*X 1 1+(5829076841/10000000000 : ℝ)*X 1 2+(2000503163/5000000000 : ℝ)*X 2 0+(-1459611803/5000000000 : ℝ)*X 2 1+(5829076841/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((7239/250000000 : ℝ)*X 0 0+(-969513197/1250000000 : ℝ)*X 0 1+(755712309/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((2908265511/5000000000 : ℝ)*X 1 0+(1804811913/5000000000 : ℝ)*X 1 1+(1674684773/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((225581513/400000000 : ℝ)*X 2 0+(-445531197/1250000000 : ℝ)*X 2 1+(-3601002937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((257256269/1000000000 : ℝ)*X 0 0+(-322144823/2500000000 : ℝ)*X 0 1+(8097991211/10000000000 : ℝ)*X 0 2+(257256269/1000000000 : ℝ)*X 1 0+(-322144823/2500000000 : ℝ)*X 1 1+(8097991211/10000000000 : ℝ)*X 1 2+(257256269/1000000000 : ℝ)*X 2 0+(-322144823/2500000000 : ℝ)*X 2 1+(8097991211/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-10733/5000000000 : ℝ)*X 0 0+(-2397537493/5000000000 : ℝ)*X 0 1+(3445842541/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((7869551567/10000000000 : ℝ)*X 1 0+(300356791/1250000000 : ℝ)*X 1 1+(1857166873/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((3683705181/5000000000 : ℝ)*X 2 0+(-3022499399/10000000000 : ℝ)*X 2 1+(-482803599/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((76341361/312500000 : ℝ)*X 0 0+(-1820016107/10000000000 : ℝ)*X 0 1+(1966356327/2500000000 : ℝ)*X 0 2+(76341361/312500000 : ℝ)*X 1 0+(-1820016107/10000000000 : ℝ)*X 1 1+(1966356327/2500000000 : ℝ)*X 1 2+(76341361/312500000 : ℝ)*X 2 0+(-1820016107/10000000000 : ℝ)*X 2 1+(1966356327/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((41335777/10000000000 : ℝ)*X 0 0+(-7575417659/10000000000 : ℝ)*X 0 1+(1996176507/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((1880133221/2500000000 : ℝ)*X 1 0+(2628562807/10000000000 : ℝ)*X 1 1+(1069805521/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((1165896139/2500000000 : ℝ)*X 2 0+(-4867987779/10000000000 : ℝ)*X 2 1+(-3318465717/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((1194967711/2000000000 : ℝ)*X 0 0+(-1894762039/10000000000 : ℝ)*X 0 1+(1174216409/2500000000 : ℝ)*X 0 2+(1194967711/2000000000 : ℝ)*X 1 0+(-1894762039/10000000000 : ℝ)*X 1 1+(1174216409/2500000000 : ℝ)*X 1 2+(1194967711/2000000000 : ℝ)*X 2 0+(-1894762039/10000000000 : ℝ)*X 2 1+(1174216409/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((2277/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2277/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (315639772073483592309906342651/45427712945510000000000000000000000 : ℝ) := by norm_num
    linear_combination (391299869203/1000000000000 : ℝ)*(base7) + (6865457/1000000000000 : ℝ)*(base40) + (534004164749/200000000000 : ℝ)*(major_s2_0) + (534004164749/200000000000 : ℝ)*(major_s2_1) + (534004164749/200000000000 : ℝ)*(major_s2_2) + (604647/100000000000 : ℝ)*(sp_s2_2) + (6684579/1000000000000 : ℝ)*(sp_s2_6) + (33955755879/10000000000 : ℝ)*(sp_s2_7) + (3395900824187/1000000000000 : ℝ)*(sp_s2_8) + (3395894025477/1000000000000 : ℝ)*(sp_s2_9) + (2094983514657/1000000000000 : ℝ)*(sp_s2_13) + (48072773/500000000000 : ℝ)*(sp_s2_20) + (325236287/1000000000000 : ℝ)*(sp_s2_21) + (752241/1000000000000 : ℝ)*(sp_s2_23) + (1703786475579/1000000000000 : ℝ)*(f.failure) + (3395900824187/1000000000000 : ℝ)*(f.sum) + (50368362015872417/512337812000000000000000000000 : ℝ)*base63 + (1177516292057/1516600000000000000000000 : ℝ)*base64 + (126228132173221/337820000000000000000000000 : ℝ)*base67 + (107894487399069/151660000000000000000000000 : ℝ)*base69 + (83692301796725357/2689462610000000000000000000000 : ℝ)*base71 + (57443521458607/141868000000000000000000000 : ℝ)*base73 + (29309221052199/168910000000000000000000000 : ℝ)*base75 + (81264716468969/354670000000000000000000000 : ℝ)*base76 + (88082801059030917/748841371250000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (39331/100000000000000000 : ℝ)*base86 + (39331/100000000000000000 : ℝ)*base88 + (39331/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1797/2500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-1797/2500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1676005007867623935519265449/147920443550000000000000000000000 : ℝ) := by norm_num
    linear_combination (374600609017/500000000000 : ℝ)*(base7) + (2383637/1000000000000 : ℝ)*(base33) + (91979456923/500000000000 : ℝ)*(base40) + (79807668331/1000000000000 : ℝ)*(base60) + (224329464097/100000000000 : ℝ)*(major_s2_0) + (2243297024607/1000000000000 : ℝ)*(major_s2_1) + (2243297024607/1000000000000 : ℝ)*(major_s2_2) + (9948511/250000000000 : ℝ)*(sp_s2_2) + (11638807/500000000000 : ℝ)*(sp_s2_6) + (213861029/1000000000000 : ℝ)*(sp_s2_13) + (2594914278657/1000000000000 : ℝ)*(sp_s2_14) + (129745594751/50000000000 : ℝ)*(sp_s2_15) + (162179506311/62500000000 : ℝ)*(sp_s2_16) + (545112679241/250000000000 : ℝ)*(sp_s2_20) + (1431486637573/1000000000000 : ℝ)*(f.failure) + (2594914278657/1000000000000 : ℝ)*(f.sum) + (50961269021981079/134825740000000000000000000000 : ℝ)*base63 + (2163017971335373/4170650000000000000000000000 : ℝ)*base65 + (1096474039133/17780000000000000000000000 : ℝ)*base66 + (29837921869073/758300000000000000000000000 : ℝ)*base68 + (60512817899262911341/147920443550000000000000000000000 : ℝ)*base71 + (29129046846007/88667500000000000000000000 : ℝ)*base72 + (5078083827479/22225000000000000000000000 : ℝ)*base74 + (23178682053843/44333750000000000000000000 : ℝ)*base77 + (17767549970662619/630603260000000000000000000000 : ℝ)*base79 + (2403/100000000000000000 : ℝ)*base87 + (2403/100000000000000000 : ℝ)*base89 + (2403/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1351/2000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1351/2000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2633859868444931674065739212327/356932030286150000000000000000000000 : ℝ) := by norm_num
    linear_combination (144939038067/200000000000 : ℝ)*(base7) + (834063/500000000000 : ℝ)*(base39) + (262771993959/500000000000 : ℝ)*(base40) + (4373271/1000000000000 : ℝ)*(base43) + (197561/500000000000 : ℝ)*(base50) + (1537456810491/500000000000 : ℝ)*(major_s2_0) + (3074909247711/1000000000000 : ℝ)*(major_s2_1) + (1537456810491/500000000000 : ℝ)*(major_s2_2) + (1260973/500000000000 : ℝ)*(sp_s2_14) + (3584727/250000000000 : ℝ)*(sp_s2_16) + (3742525539687/1000000000000 : ℝ)*(sp_s2_21) + (467816554363/125000000000 : ℝ)*(sp_s2_22) + (149700548909/40000000000 : ℝ)*(sp_s2_23) + (2686850763959/1000000000000 : ℝ)*(sp_s2_27) + (245269446703/125000000000 : ℝ)*(f.failure) + (467816554363/125000000000 : ℝ)*(f.sum) + (168141310524791441/914888950000000000000000000000 : ℝ)*base62 + (95624480711379/521331250000000000000000000 : ℝ)*base64 + (1493200733769/1930400000000000000000000 : ℝ)*base67 + (19760575759777/47393750000000000000000000 : ℝ)*base69 + (46761490593994355583/147920443550000000000000000000000 : ℝ)*base70 + (363424533398161/1773350000000000000000000000 : ℝ)*base73 + (22306811709787/120650000000000000000000000 : ℝ)*base75 + (48421161100583/110834375000000000000000000 : ℝ)*base76 + (2061917941195822611/8558187100000000000000000000000 : ℝ)*base79 + (1167/12500000000000000 : ℝ)*base86 + (1167/12500000000000000 : ℝ)*base88 + (1167/12500000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((35467/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(35467/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-16891/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-16891/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(83413/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(83413/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2277/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2277/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1797/2500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-1797/2500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1351/2000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1351/2000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c308086_s2 p hpa hpb X hX hprev1

#print axioms solution

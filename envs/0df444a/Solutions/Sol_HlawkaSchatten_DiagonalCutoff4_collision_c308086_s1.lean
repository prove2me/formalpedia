-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c308086_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:40:29.915984+00:00
-- url     : https://prove2.me/submissions/5a3ebd41-13a9-41bf-9895-030547ecd1c1

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
theorem collision_support_c308086_s1_s1_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1621738081/2500000000 : ℝ)*x 0 + (3132955529/10000000000 : ℝ)*x 1 + (754094117/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1621738081/2500000000 : ℝ)^69 ≤ (14231093971097/25000000000000 : ℝ)^53 := by
    have hnat : (1621738081 : ℕ)^69*25000000000000^53 ≤ 14231093971097^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1621738081 2500000000 14231093971097 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3132955529/10000000000 : ℝ)^69 ≤ (22069346310081/100000000000000 : ℝ)^53 := by
    have hnat : (3132955529 : ℕ)^69*100000000000000^53 ≤ 22069346310081^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3132955529 10000000000 22069346310081 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (754094117/2500000000 : ℝ)^69 ≤ (21006277795731/100000000000000 : ℝ)^53 := by
    have hnat : (754094117 : ℕ)^69*100000000000000^53 ≤ 21006277795731^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      754094117 2500000000 21006277795731 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1621738081/2500000000 : ℝ), (3132955529/10000000000 : ℝ), (754094117/2500000000 : ℝ)] ![(14231093971097/25000000000000 : ℝ), (22069346310081/100000000000000 : ℝ), (21006277795731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1621738081/2500000000 : ℝ)|^69 ≤ (14231093971097/25000000000000 : ℝ)^53
        have hw : |(1621738081/2500000000 : ℝ)|=(1621738081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3132955529/10000000000 : ℝ)|^69 ≤ (22069346310081/100000000000000 : ℝ)^53
        have hw : |(3132955529/10000000000 : ℝ)|=(3132955529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(754094117/2500000000 : ℝ)|^69 ≤ (21006277795731/100000000000000 : ℝ)^53
        have hw : |(754094117/2500000000 : ℝ)|=(754094117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s1_s1_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6198392881/10000000000 : ℝ)*x 0 + (-3359523649/10000000000 : ℝ)*x 1 + (-629011163/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6198392881/10000000000 : ℝ)^69 ≤ (838283523383/1562500000000 : ℝ)^53 := by
    have hnat : (6198392881 : ℕ)^69*1562500000000^53 ≤ 838283523383^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6198392881 10000000000 838283523383 1562500000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3359523649/10000000000 : ℝ)^69 ≤ (24169473931369/100000000000000 : ℝ)^53 := by
    have hnat : (3359523649 : ℕ)^69*100000000000000^53 ≤ 24169473931369^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3359523649 10000000000 24169473931369 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (629011163/2000000000 : ℝ)^69 ≤ (110901902823/500000000000 : ℝ)^53 := by
    have hnat : (629011163 : ℕ)^69*500000000000^53 ≤ 110901902823^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      629011163 2000000000 110901902823 500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6198392881/10000000000 : ℝ), (-3359523649/10000000000 : ℝ), (-629011163/2000000000 : ℝ)] ![(838283523383/1562500000000 : ℝ), (24169473931369/100000000000000 : ℝ), (110901902823/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6198392881/10000000000 : ℝ)|^69 ≤ (838283523383/1562500000000 : ℝ)^53
        have hw : |(6198392881/10000000000 : ℝ)|=(6198392881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3359523649/10000000000 : ℝ)|^69 ≤ (24169473931369/100000000000000 : ℝ)^53
        have hw : |(-3359523649/10000000000 : ℝ)|=(3359523649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-629011163/2000000000 : ℝ)|^69 ≤ (110901902823/500000000000 : ℝ)^53
        have hw : |(-629011163/2000000000 : ℝ)|=(629011163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s1_s1_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (891185229/2500000000 : ℝ)*x 0 + (-1309750017/5000000000 : ℝ)*x 1 + (1610451301/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (891185229/2500000000 : ℝ)^69 ≤ (13054526866459/50000000000000 : ℝ)^53 := by
    have hnat : (891185229 : ℕ)^69*50000000000000^53 ≤ 13054526866459^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      891185229 2500000000 13054526866459 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1309750017/5000000000 : ℝ)^69 ≤ (17481803318297/100000000000000 : ℝ)^53 := by
    have hnat : (1309750017 : ℕ)^69*100000000000000^53 ≤ 17481803318297^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309750017 5000000000 17481803318297 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1610451301/2500000000 : ℝ)^69 ≤ (56409142935399/100000000000000 : ℝ)^53 := by
    have hnat : (1610451301 : ℕ)^69*100000000000000^53 ≤ 56409142935399^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1610451301 2500000000 56409142935399 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(891185229/2500000000 : ℝ), (-1309750017/5000000000 : ℝ), (1610451301/2500000000 : ℝ)] ![(13054526866459/50000000000000 : ℝ), (17481803318297/100000000000000 : ℝ), (56409142935399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(891185229/2500000000 : ℝ)|^69 ≤ (13054526866459/50000000000000 : ℝ)^53
        have hw : |(891185229/2500000000 : ℝ)|=(891185229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1309750017/5000000000 : ℝ)|^69 ≤ (17481803318297/100000000000000 : ℝ)^53
        have hw : |(-1309750017/5000000000 : ℝ)|=(1309750017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1610451301/2500000000 : ℝ)|^69 ≤ (56409142935399/100000000000000 : ℝ)^53
        have hw : |(1610451301/2500000000 : ℝ)|=(1610451301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s1_s1_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (42082523/10000000000 : ℝ)*x 0 + (-8304088281/10000000000 : ℝ)*x 1 + (765171379/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42082523/10000000000 : ℝ)^69 ≤ (80695529091/100000000000000 : ℝ)^53 := by
    have hnat : (42082523 : ℕ)^69*100000000000000^53 ≤ 80695529091^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42082523 10000000000 80695529091 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8304088281/10000000000 : ℝ)^69 ≤ (78510413634339/100000000000000 : ℝ)^53 := by
    have hnat : (8304088281 : ℕ)^69*100000000000000^53 ≤ 78510413634339^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8304088281 10000000000 78510413634339 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (765171379/2500000000 : ℝ)^69 ≤ (535222270597/2500000000000 : ℝ)^53 := by
    have hnat : (765171379 : ℕ)^69*2500000000000^53 ≤ 535222270597^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      765171379 2500000000 535222270597 2500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42082523/10000000000 : ℝ), (-8304088281/10000000000 : ℝ), (765171379/2500000000 : ℝ)] ![(80695529091/100000000000000 : ℝ), (78510413634339/100000000000000 : ℝ), (535222270597/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42082523/10000000000 : ℝ)|^69 ≤ (80695529091/100000000000000 : ℝ)^53
        have hw : |(42082523/10000000000 : ℝ)|=(42082523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8304088281/10000000000 : ℝ)|^69 ≤ (78510413634339/100000000000000 : ℝ)^53
        have hw : |(-8304088281/10000000000 : ℝ)|=(8304088281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(765171379/2500000000 : ℝ)|^69 ≤ (535222270597/2500000000000 : ℝ)^53
        have hw : |(765171379/2500000000 : ℝ)|=(765171379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s1_s1_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (163396581/400000000 : ℝ)*x 0 + (3076931143/5000000000 : ℝ)*x 1 + (2409089331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (163396581/400000000 : ℝ)^69 ≤ (15587420551723/50000000000000 : ℝ)^53 := by
    have hnat : (163396581 : ℕ)^69*50000000000000^53 ≤ 15587420551723^53*400000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163396581 400000000 15587420551723 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3076931143/5000000000 : ℝ)^69 ≤ (2125955951991/4000000000000 : ℝ)^53 := by
    have hnat : (3076931143 : ℕ)^69*4000000000000^53 ≤ 2125955951991^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3076931143 5000000000 2125955951991 4000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2409089331/10000000000 : ℝ)^69 ≤ (15676260086919/100000000000000 : ℝ)^53 := by
    have hnat : (2409089331 : ℕ)^69*100000000000000^53 ≤ 15676260086919^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2409089331 10000000000 15676260086919 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(163396581/400000000 : ℝ), (3076931143/5000000000 : ℝ), (2409089331/10000000000 : ℝ)] ![(15587420551723/50000000000000 : ℝ), (2125955951991/4000000000000 : ℝ), (15676260086919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(163396581/400000000 : ℝ)|^69 ≤ (15587420551723/50000000000000 : ℝ)^53
        have hw : |(163396581/400000000 : ℝ)|=(163396581/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3076931143/5000000000 : ℝ)|^69 ≤ (2125955951991/4000000000000 : ℝ)^53
        have hw : |(3076931143/5000000000 : ℝ)|=(3076931143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2409089331/10000000000 : ℝ)|^69 ≤ (15676260086919/100000000000000 : ℝ)^53
        have hw : |(2409089331/10000000000 : ℝ)|=(2409089331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s1_s1_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1656594847/2000000000 : ℝ)*x 0 + (-598877277/5000000000 : ℝ)*x 1 + (-2380887941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1656594847/2000000000 : ℝ)^69 ≤ (39125314582591/50000000000000 : ℝ)^53 := by
    have hnat : (1656594847 : ℕ)^69*50000000000000^53 ≤ 39125314582591^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1656594847 2000000000 39125314582591 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (598877277/5000000000 : ℝ)^69 ≤ (1262319371831/20000000000000 : ℝ)^53 := by
    have hnat : (598877277 : ℕ)^69*20000000000000^53 ≤ 1262319371831^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598877277 5000000000 1262319371831 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2380887941/10000000000 : ℝ)^69 ≤ (7718886980591/50000000000000 : ℝ)^53 := by
    have hnat : (2380887941 : ℕ)^69*50000000000000^53 ≤ 7718886980591^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2380887941 10000000000 7718886980591 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1656594847/2000000000 : ℝ), (-598877277/5000000000 : ℝ), (-2380887941/10000000000 : ℝ)] ![(39125314582591/50000000000000 : ℝ), (1262319371831/20000000000000 : ℝ), (7718886980591/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1656594847/2000000000 : ℝ)|^69 ≤ (39125314582591/50000000000000 : ℝ)^53
        have hw : |(1656594847/2000000000 : ℝ)|=(1656594847/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-598877277/5000000000 : ℝ)|^69 ≤ (1262319371831/20000000000000 : ℝ)^53
        have hw : |(-598877277/5000000000 : ℝ)|=(598877277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2380887941/10000000000 : ℝ)|^69 ≤ (7718886980591/50000000000000 : ℝ)^53
        have hw : |(-2380887941/10000000000 : ℝ)|=(2380887941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s1_s1_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (433918059/1250000000 : ℝ)*x 0 + (-215662841/2000000000 : ℝ)*x 1 + (471427979/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (433918059/1250000000 : ℝ)^69 ≤ (6305507535483/25000000000000 : ℝ)^53 := by
    have hnat : (433918059 : ℕ)^69*25000000000000^53 ≤ 6305507535483^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433918059 1250000000 6305507535483 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215662841/2000000000 : ℝ)^69 ≤ (5504830048161/100000000000000 : ℝ)^53 := by
    have hnat : (215662841 : ℕ)^69*100000000000000^53 ≤ 5504830048161^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215662841 2000000000 5504830048161 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (471427979/625000000 : ℝ)^69 ≤ (6927313978909/10000000000000 : ℝ)^53 := by
    have hnat : (471427979 : ℕ)^69*10000000000000^53 ≤ 6927313978909^53*625000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471427979 625000000 6927313978909 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(433918059/1250000000 : ℝ), (-215662841/2000000000 : ℝ), (471427979/625000000 : ℝ)] ![(6305507535483/25000000000000 : ℝ), (5504830048161/100000000000000 : ℝ), (6927313978909/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(433918059/1250000000 : ℝ)|^69 ≤ (6305507535483/25000000000000 : ℝ)^53
        have hw : |(433918059/1250000000 : ℝ)|=(433918059/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-215662841/2000000000 : ℝ)|^69 ≤ (5504830048161/100000000000000 : ℝ)^53
        have hw : |(-215662841/2000000000 : ℝ)|=(215662841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(471427979/625000000 : ℝ)|^69 ≤ (6927313978909/10000000000000 : ℝ)^53
        have hw : |(471427979/625000000 : ℝ)|=(471427979/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s1_s1_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-205459/2500000000 : ℝ)*x 0 + (-4202399871/10000000000 : ℝ)*x 1 + (1851729813/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (205459/2500000000 : ℝ)^69 ≤ (480300189/100000000000000 : ℝ)^53 := by
    have hnat : (205459 : ℕ)^69*100000000000000^53 ≤ 480300189^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205459 2500000000 480300189 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4202399871/10000000000 : ℝ)^69 ≤ (323471635591/1000000000000 : ℝ)^53 := by
    have hnat : (4202399871 : ℕ)^69*1000000000000^53 ≤ 323471635591^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4202399871 10000000000 323471635591 1000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1851729813/2500000000 : ℝ)^69 ≤ (33826178066221/50000000000000 : ℝ)^53 := by
    have hnat : (1851729813 : ℕ)^69*50000000000000^53 ≤ 33826178066221^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1851729813 2500000000 33826178066221 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-205459/2500000000 : ℝ), (-4202399871/10000000000 : ℝ), (1851729813/2500000000 : ℝ)] ![(480300189/100000000000000 : ℝ), (323471635591/1000000000000 : ℝ), (33826178066221/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-205459/2500000000 : ℝ)|^69 ≤ (480300189/100000000000000 : ℝ)^53
        have hw : |(-205459/2500000000 : ℝ)|=(205459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4202399871/10000000000 : ℝ)|^69 ≤ (323471635591/1000000000000 : ℝ)^53
        have hw : |(-4202399871/10000000000 : ℝ)|=(4202399871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1851729813/2500000000 : ℝ)|^69 ≤ (33826178066221/50000000000000 : ℝ)^53
        have hw : |(1851729813/2500000000 : ℝ)|=(1851729813/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s1_s1_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2194417397/2500000000 : ℝ)*x 0 + (1868850799/10000000000 : ℝ)*x 1 + (899511503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2194417397/2500000000 : ℝ)^69 ≤ (84389063234383/100000000000000 : ℝ)^53 := by
    have hnat : (2194417397 : ℕ)^69*100000000000000^53 ≤ 84389063234383^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194417397 2500000000 84389063234383 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1868850799/10000000000 : ℝ)^69 ≤ (11263481037699/100000000000000 : ℝ)^53 := by
    have hnat : (1868850799 : ℕ)^69*100000000000000^53 ≤ 11263481037699^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1868850799 10000000000 11263481037699 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (899511503/10000000000 : ℝ)^69 ≤ (4347455704299/100000000000000 : ℝ)^53 := by
    have hnat : (899511503 : ℕ)^69*100000000000000^53 ≤ 4347455704299^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899511503 10000000000 4347455704299 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2194417397/2500000000 : ℝ), (1868850799/10000000000 : ℝ), (899511503/10000000000 : ℝ)] ![(84389063234383/100000000000000 : ℝ), (11263481037699/100000000000000 : ℝ), (4347455704299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2194417397/2500000000 : ℝ)|^69 ≤ (84389063234383/100000000000000 : ℝ)^53
        have hw : |(2194417397/2500000000 : ℝ)|=(2194417397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1868850799/10000000000 : ℝ)|^69 ≤ (11263481037699/100000000000000 : ℝ)^53
        have hw : |(1868850799/10000000000 : ℝ)|=(1868850799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(899511503/10000000000 : ℝ)|^69 ≤ (4347455704299/100000000000000 : ℝ)^53
        have hw : |(899511503/10000000000 : ℝ)|=(899511503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s1_s1_16 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4188715279/5000000000 : ℝ)*x 0 + (-1954025531/10000000000 : ℝ)*x 1 + (-23839551/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4188715279/5000000000 : ℝ)^69 ≤ (79414355133613/100000000000000 : ℝ)^53 := by
    have hnat : (4188715279 : ℕ)^69*100000000000000^53 ≤ 79414355133613^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4188715279 5000000000 79414355133613 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1954025531/10000000000 : ℝ)^69 ≤ (37301084451/312500000000 : ℝ)^53 := by
    have hnat : (1954025531 : ℕ)^69*312500000000^53 ≤ 37301084451^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1954025531 10000000000 37301084451 312500000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (23839551/156250000 : ℝ)^69 ≤ (8649297826983/100000000000000 : ℝ)^53 := by
    have hnat : (23839551 : ℕ)^69*100000000000000^53 ≤ 8649297826983^53*156250000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23839551 156250000 8649297826983 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4188715279/5000000000 : ℝ), (-1954025531/10000000000 : ℝ), (-23839551/156250000 : ℝ)] ![(79414355133613/100000000000000 : ℝ), (37301084451/312500000000 : ℝ), (8649297826983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4188715279/5000000000 : ℝ)|^69 ≤ (79414355133613/100000000000000 : ℝ)^53
        have hw : |(4188715279/5000000000 : ℝ)|=(4188715279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1954025531/10000000000 : ℝ)|^69 ≤ (37301084451/312500000000 : ℝ)^53
        have hw : |(-1954025531/10000000000 : ℝ)|=(1954025531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-23839551/156250000 : ℝ)|^69 ≤ (8649297826983/100000000000000 : ℝ)^53
        have hw : |(-23839551/156250000 : ℝ)|=(23839551/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s1_s1_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2114074887/10000000000 : ℝ)*x 0 + (-1382459657/10000000000 : ℝ)*x 1 + (2089368389/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2114074887/10000000000 : ℝ)^69 ≤ (13224617500759/100000000000000 : ℝ)^53 := by
    have hnat : (2114074887 : ℕ)^69*100000000000000^53 ≤ 13224617500759^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114074887 10000000000 13224617500759 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1382459657/10000000000 : ℝ)^69 ≤ (3803617180811/50000000000000 : ℝ)^53 := by
    have hnat : (1382459657 : ℕ)^69*50000000000000^53 ≤ 3803617180811^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1382459657 10000000000 3803617180811 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2089368389/2500000000 : ℝ)^69 ≤ (19792037030111/25000000000000 : ℝ)^53 := by
    have hnat : (2089368389 : ℕ)^69*25000000000000^53 ≤ 19792037030111^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089368389 2500000000 19792037030111 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2114074887/10000000000 : ℝ), (-1382459657/10000000000 : ℝ), (2089368389/2500000000 : ℝ)] ![(13224617500759/100000000000000 : ℝ), (3803617180811/50000000000000 : ℝ), (19792037030111/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2114074887/10000000000 : ℝ)|^69 ≤ (13224617500759/100000000000000 : ℝ)^53
        have hw : |(2114074887/10000000000 : ℝ)|=(2114074887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1382459657/10000000000 : ℝ)|^69 ≤ (3803617180811/50000000000000 : ℝ)^53
        have hw : |(-1382459657/10000000000 : ℝ)|=(1382459657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2089368389/2500000000 : ℝ)|^69 ≤ (19792037030111/25000000000000 : ℝ)^53
        have hw : |(2089368389/2500000000 : ℝ)|=(2089368389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s1_s1_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (19818727/10000000000 : ℝ)*x 0 + (-8418391299/10000000000 : ℝ)*x 1 + (582055483/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (19818727/10000000000 : ℝ)^69 ≤ (7569002237/25000000000000 : ℝ)^53 := by
    have hnat : (19818727 : ℕ)^69*25000000000000^53 ≤ 7569002237^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19818727 10000000000 7569002237 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8418391299/10000000000 : ℝ)^69 ≤ (79920237150273/100000000000000 : ℝ)^53 := by
    have hnat : (8418391299 : ℕ)^69*100000000000000^53 ≤ 79920237150273^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8418391299 10000000000 79920237150273 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (582055483/2000000000 : ℝ)^69 ≤ (20049486825483/100000000000000 : ℝ)^53 := by
    have hnat : (582055483 : ℕ)^69*100000000000000^53 ≤ 20049486825483^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      582055483 2000000000 20049486825483 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(19818727/10000000000 : ℝ), (-8418391299/10000000000 : ℝ), (582055483/2000000000 : ℝ)] ![(7569002237/25000000000000 : ℝ), (79920237150273/100000000000000 : ℝ), (20049486825483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(19818727/10000000000 : ℝ)|^69 ≤ (7569002237/25000000000000 : ℝ)^53
        have hw : |(19818727/10000000000 : ℝ)|=(19818727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8418391299/10000000000 : ℝ)|^69 ≤ (79920237150273/100000000000000 : ℝ)^53
        have hw : |(-8418391299/10000000000 : ℝ)|=(8418391299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(582055483/2000000000 : ℝ)|^69 ≤ (20049486825483/100000000000000 : ℝ)^53
        have hw : |(582055483/2000000000 : ℝ)|=(582055483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s1_s1_22 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (866126679/1000000000 : ℝ)*x 0 + (747801927/5000000000 : ℝ)*x 1 + (1524111383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (866126679/1000000000 : ℝ)^69 ≤ (82935042239601/100000000000000 : ℝ)^53 := by
    have hnat : (866126679 : ℕ)^69*100000000000000^53 ≤ 82935042239601^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866126679 1000000000 82935042239601 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (747801927/5000000000 : ℝ)^69 ≤ (1685522654537/20000000000000 : ℝ)^53 := by
    have hnat : (747801927 : ℕ)^69*20000000000000^53 ≤ 1685522654537^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      747801927 5000000000 1685522654537 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1524111383/10000000000 : ℝ)^69 ≤ (8637344480261/100000000000000 : ℝ)^53 := by
    have hnat : (1524111383 : ℕ)^69*100000000000000^53 ≤ 8637344480261^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1524111383 10000000000 8637344480261 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(866126679/1000000000 : ℝ), (747801927/5000000000 : ℝ), (1524111383/10000000000 : ℝ)] ![(82935042239601/100000000000000 : ℝ), (1685522654537/20000000000000 : ℝ), (8637344480261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(866126679/1000000000 : ℝ)|^69 ≤ (82935042239601/100000000000000 : ℝ)^53
        have hw : |(866126679/1000000000 : ℝ)|=(866126679/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(747801927/5000000000 : ℝ)|^69 ≤ (1685522654537/20000000000000 : ℝ)^53
        have hw : |(747801927/5000000000 : ℝ)|=(747801927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1524111383/10000000000 : ℝ)|^69 ≤ (8637344480261/100000000000000 : ℝ)^53
        have hw : |(1524111383/10000000000 : ℝ)|=(1524111383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s1_s1_23 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (879419197/2000000000 : ℝ)*x 0 + (-415353137/1000000000 : ℝ)*x 1 + (-2174798689/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (879419197/2000000000 : ℝ)^69 ≤ (34311717536997/100000000000000 : ℝ)^53 := by
    have hnat : (879419197 : ℕ)^69*100000000000000^53 ≤ 34311717536997^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      879419197 2000000000 34311717536997 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (415353137/1000000000 : ℝ)^69 ≤ (15929156557007/50000000000000 : ℝ)^53 := by
    have hnat : (415353137 : ℕ)^69*50000000000000^53 ≤ 15929156557007^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415353137 1000000000 15929156557007 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2174798689/5000000000 : ℝ)^69 ≤ (33829969330381/100000000000000 : ℝ)^53 := by
    have hnat : (2174798689 : ℕ)^69*100000000000000^53 ≤ 33829969330381^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174798689 5000000000 33829969330381 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(879419197/2000000000 : ℝ), (-415353137/1000000000 : ℝ), (-2174798689/5000000000 : ℝ)] ![(34311717536997/100000000000000 : ℝ), (15929156557007/50000000000000 : ℝ), (33829969330381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(879419197/2000000000 : ℝ)|^69 ≤ (34311717536997/100000000000000 : ℝ)^53
        have hw : |(879419197/2000000000 : ℝ)|=(879419197/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-415353137/1000000000 : ℝ)|^69 ≤ (15929156557007/50000000000000 : ℝ)^53
        have hw : |(-415353137/1000000000 : ℝ)|=(415353137/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2174798689/5000000000 : ℝ)|^69 ≤ (33829969330381/100000000000000 : ℝ)^53
        have hw : |(-2174798689/5000000000 : ℝ)|=(2174798689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s1_s1_27 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7282789757/10000000000 : ℝ)*x 0 + (-1029788757/10000000000 : ℝ)*x 1 + (3826824527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7282789757/10000000000 : ℝ)^69 ≤ (3309004009149/5000000000000 : ℝ)^53 := by
    have hnat : (7282789757 : ℕ)^69*5000000000000^53 ≤ 3309004009149^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7282789757 10000000000 3309004009149 5000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1029788757/10000000000 : ℝ)^69 ≤ (2592267737319/50000000000000 : ℝ)^53 := by
    have hnat : (1029788757 : ℕ)^69*50000000000000^53 ≤ 2592267737319^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029788757 10000000000 2592267737319 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3826824527/10000000000 : ℝ)^69 ≤ (28635384328569/100000000000000 : ℝ)^53 := by
    have hnat : (3826824527 : ℕ)^69*100000000000000^53 ≤ 28635384328569^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3826824527 10000000000 28635384328569 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7282789757/10000000000 : ℝ), (-1029788757/10000000000 : ℝ), (3826824527/10000000000 : ℝ)] ![(3309004009149/5000000000000 : ℝ), (2592267737319/50000000000000 : ℝ), (28635384328569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7282789757/10000000000 : ℝ)|^69 ≤ (3309004009149/5000000000000 : ℝ)^53
        have hw : |(7282789757/10000000000 : ℝ)|=(7282789757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1029788757/10000000000 : ℝ)|^69 ≤ (2592267737319/50000000000000 : ℝ)^53
        have hw : |(-1029788757/10000000000 : ℝ)|=(1029788757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3826824527/10000000000 : ℝ)|^69 ≤ (28635384328569/100000000000000 : ℝ)^53
        have hw : |(3826824527/10000000000 : ℝ)|=(3826824527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308086_s1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((87567/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(87567/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-93489/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-93489/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(46237/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(46237/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((35467/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(35467/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-16891/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-16891/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(83413/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(83413/100000 : ℝ)*X 1 2) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (87567/100000 : ℝ) ^ (17/4 : ℝ) ≤ (7109793971270024417/12500000000000000000 : ℝ) := by
    have hpowers : (87567/100000 : ℝ)^17 ≤ (7109793971270024417/12500000000000000000 : ℝ)^4 := by
      have hnat : (87567 : ℕ)^17*12500000000000000000^4 ≤ 7109793971270024417^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        87567 100000 7109793971270024417 12500000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (87567/100000 : ℝ)) (X := (7109793971270024417/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (19609793971270024417/12500000000000000000 : ℝ) ≤ (5558848423835201/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (19609793971270024417/12500000000000000000 : ℝ)^4 ≤ (5558848423835201/5000000000000000 : ℝ)^17 := by
      have hnat : (19609793971270024417 : ℕ)^4*5000000000000000^17 ≤ 5558848423835201^17*12500000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19609793971270024417 12500000000000000000 5558848423835201 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5558848423835201/5000000000000000 : ℝ)) (X := (19609793971270024417/12500000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (13359793971270024417/6250000000000000000 : ℝ) ≤ (597858184857407/500000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (13359793971270024417/6250000000000000000 : ℝ)^4 ≤ (597858184857407/500000000000000 : ℝ)^17 := by
      have hnat : (13359793971270024417 : ℕ)^4*500000000000000^17 ≤ 597858184857407^17*6250000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13359793971270024417 6250000000000000000 597858184857407 500000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (597858184857407/500000000000000 : ℝ)) (X := (13359793971270024417/6250000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(186282807945067/1459450000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(139911141579623/1459450000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (87567/100000 : ℝ)) (alpha := (186282807945067/1459450000000000 : ℝ)) (beta := (139911141579623/1459450000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (87567/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(186282807945067/1459450000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(139911141579623/1459450000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (93489/100000 : ℝ) ^ (17/4 : ℝ) ≤ (18778988451498766253/25000000000000000000 : ℝ) := by
    have hpowers : (93489/100000 : ℝ)^17 ≤ (18778988451498766253/25000000000000000000 : ℝ)^4 := by
      have hnat : (93489 : ℕ)^17*25000000000000000000^4 ≤ 18778988451498766253^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        93489 100000 18778988451498766253 25000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (93489/100000 : ℝ)) (X := (18778988451498766253/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (43778988451498766253/25000000000000000000 : ℝ) ≤ (11409145249732563/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (43778988451498766253/25000000000000000000 : ℝ)^4 ≤ (11409145249732563/10000000000000000 : ℝ)^17 := by
      have hnat : (43778988451498766253 : ℕ)^4*10000000000000000^17 ≤ 11409145249732563^17*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        43778988451498766253 25000000000000000000 11409145249732563 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11409145249732563/10000000000000000 : ℝ)) (X := (43778988451498766253/25000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (31278988451498766253/12500000000000000000 : ℝ) ≤ (12408740174159871/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (31278988451498766253/12500000000000000000 : ℝ)^4 ≤ (12408740174159871/10000000000000000 : ℝ)^17 := by
      have hnat : (31278988451498766253 : ℕ)^4*10000000000000000^17 ≤ 12408740174159871^17*12500000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31278988451498766253 12500000000000000000 12408740174159871 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12408740174159871/10000000000000000 : ℝ)) (X := (31278988451498766253/12500000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1409145249732563/9348900000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(7572688821419/70825000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (93489/100000 : ℝ)) (alpha := (1409145249732563/9348900000000000 : ℝ)) (beta := (7572688821419/70825000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (93489/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1409145249732563/9348900000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(7572688821419/70825000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (46237/50000 : ℝ) ^ (17/4 : ℝ) ≤ (71710621321960964369/100000000000000000000 : ℝ) := by
    have hpowers : (46237/50000 : ℝ)^17 ≤ (71710621321960964369/100000000000000000000 : ℝ)^4 := by
      have hnat : (46237 : ℕ)^17*100000000000000000000^4 ≤ 71710621321960964369^4*50000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        46237 50000 71710621321960964369 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (46237/50000 : ℝ)) (X := (71710621321960964369/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (171710621321960964369/100000000000000000000 : ℝ) ≤ (113565492987241/100000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (171710621321960964369/100000000000000000000 : ℝ)^4 ≤ (113565492987241/100000000000000 : ℝ)^17 := by
      have hnat : (171710621321960964369 : ℕ)^4*100000000000000^17 ≤ 113565492987241^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        171710621321960964369 100000000000000000000 113565492987241 100000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (113565492987241/100000000000000 : ℝ)) (X := (171710621321960964369/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (121710621321960964369/50000000000000000000 : ℝ) ≤ (308210823016063/250000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (121710621321960964369/50000000000000000000 : ℝ)^4 ≤ (308210823016063/250000000000000 : ℝ)^17 := by
      have hnat : (121710621321960964369 : ℕ)^4*250000000000000^17 ≤ 308210823016063^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        121710621321960964369 50000000000000000000 308210823016063 250000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (308210823016063/250000000000000 : ℝ)) (X := (121710621321960964369/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(13565492987241/92474000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(48594181095921/462370000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (46237/50000 : ℝ)) (alpha := (13565492987241/92474000000000 : ℝ)) (beta := (48594181095921/462370000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (46237/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(13565492987241/92474000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(48594181095921/462370000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_1 : ((1621738081/2500000000 : ℝ)*X 1 0+(3132955529/10000000000 : ℝ)*X 1 1+(754094117/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((6198392881/10000000000 : ℝ)*X 2 0+(-3359523649/10000000000 : ℝ)*X 2 1+(-629011163/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((891185229/2500000000 : ℝ)*X 0 0+(-1309750017/5000000000 : ℝ)*X 0 1+(1610451301/2500000000 : ℝ)*X 0 2+(891185229/2500000000 : ℝ)*X 1 0+(-1309750017/5000000000 : ℝ)*X 1 1+(1610451301/2500000000 : ℝ)*X 1 2+(891185229/2500000000 : ℝ)*X 2 0+(-1309750017/5000000000 : ℝ)*X 2 1+(1610451301/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((42082523/10000000000 : ℝ)*X 0 0+(-8304088281/10000000000 : ℝ)*X 0 1+(765171379/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((163396581/400000000 : ℝ)*X 1 0+(3076931143/5000000000 : ℝ)*X 1 1+(2409089331/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((1656594847/2000000000 : ℝ)*X 2 0+(-598877277/5000000000 : ℝ)*X 2 1+(-2380887941/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((433918059/1250000000 : ℝ)*X 0 0+(-215662841/2000000000 : ℝ)*X 0 1+(471427979/625000000 : ℝ)*X 0 2+(433918059/1250000000 : ℝ)*X 1 0+(-215662841/2000000000 : ℝ)*X 1 1+(471427979/625000000 : ℝ)*X 1 2+(433918059/1250000000 : ℝ)*X 2 0+(-215662841/2000000000 : ℝ)*X 2 1+(471427979/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-205459/2500000000 : ℝ)*X 0 0+(-4202399871/10000000000 : ℝ)*X 0 1+(1851729813/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((2194417397/2500000000 : ℝ)*X 1 0+(1868850799/10000000000 : ℝ)*X 1 1+(899511503/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((4188715279/5000000000 : ℝ)*X 2 0+(-1954025531/10000000000 : ℝ)*X 2 1+(-23839551/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((2114074887/10000000000 : ℝ)*X 0 0+(-1382459657/10000000000 : ℝ)*X 0 1+(2089368389/2500000000 : ℝ)*X 0 2+(2114074887/10000000000 : ℝ)*X 1 0+(-1382459657/10000000000 : ℝ)*X 1 1+(2089368389/2500000000 : ℝ)*X 1 2+(2114074887/10000000000 : ℝ)*X 2 0+(-1382459657/10000000000 : ℝ)*X 2 1+(2089368389/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((19818727/10000000000 : ℝ)*X 0 0+(-8418391299/10000000000 : ℝ)*X 0 1+(582055483/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((866126679/1000000000 : ℝ)*X 1 0+(747801927/5000000000 : ℝ)*X 1 1+(1524111383/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((879419197/2000000000 : ℝ)*X 2 0+(-415353137/1000000000 : ℝ)*X 2 1+(-2174798689/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((7282789757/10000000000 : ℝ)*X 0 0+(-1029788757/10000000000 : ℝ)*X 0 1+(3826824527/10000000000 : ℝ)*X 0 2+(7282789757/10000000000 : ℝ)*X 1 0+(-1029788757/10000000000 : ℝ)*X 1 1+(3826824527/10000000000 : ℝ)*X 1 2+(7282789757/10000000000 : ℝ)*X 2 0+(-1029788757/10000000000 : ℝ)*X 2 1+(3826824527/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((35467/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(35467/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8386362870075328443577274133091/1051448807631475000000000000000000000 : ℝ) := by norm_num
    linear_combination (482652730193/1000000000000 : ℝ)*(base7) + (14723747289/62500000000 : ℝ)*(base43) + (733206848171/1000000000000 : ℝ)*(base54) + (330101393987/200000000000 : ℝ)*(major_s1_0) + (1414927013311/1000000000000 : ℝ)*(major_s1_1) + (229325030441/250000000000 : ℝ)*(major_s1_2) + (67906031/1000000000000 : ℝ)*(sp_s1_2) + (7355439/200000000000 : ℝ)*(sp_s1_6) + (2680707187/1562500000 : ℝ)*(sp_s1_7) + (1951329619021/1000000000000 : ℝ)*(sp_s1_8) + (245618727049/250000000000 : ℝ)*(sp_s1_9) + (783791137/976562500 : ℝ)*(sp_s1_13) + (4805943/200000000000 : ℝ)*(sp_s1_20) + (48531359/500000000000 : ℝ)*(sp_s1_21) + (131652131147/125000000000 : ℝ)*(f.failure) + (1951329619021/1000000000000 : ℝ)*(f.sum) + (1500797015528714131/6549471050000000000000000000000 : ℝ)*base63 + (984159522813/18494800000000000000000000 : ℝ)*base64 + (6764338963930313/9348900000000000000000000000 : ℝ)*base67 + (190716522291169/231185000000000000000000000 : ℝ)*base69 + (711881947099302281/3374029482500000000000000000000 : ℝ)*base71 + (135845760990917/145945000000000000000000000 : ℝ)*base73 + (42418380980919/70825000000000000000000000 : ℝ)*base75 + (33751469796679/291890000000000000000000000 : ℝ)*base76 + (171444121767874131757/272885042100000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (9983/12500000000000000 : ℝ)*base86 + (9983/12500000000000000 : ℝ)*base88 + (9983/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-16891/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-16891/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (573557515902959268538248559461/38234502095690000000000000000000000 : ℝ) := by norm_num
    linear_combination (186056293517/200000000000 : ℝ)*(base7) + (20489695753/1000000000000 : ℝ)*(base33) + (139797/250000000000 : ℝ)*(base40) + (613377/1000000000000 : ℝ)*(base49) + (124354387/200000000000 : ℝ)*(base60) + (1629771114489/1000000000000 : ℝ)*(major_s1_0) + (825130405121/500000000000 : ℝ)*(major_s1_1) + (825130405121/500000000000 : ℝ)*(major_s1_2) + (3412479/500000000000 : ℝ)*(sp_s1_1) + (1676040561061/1000000000000 : ℝ)*(sp_s1_14) + (1655434728221/1000000000000 : ℝ)*(sp_s1_15) + (413887716327/250000000000 : ℝ)*(sp_s1_16) + (1983341438003/1000000000000 : ℝ)*(sp_s1_20) + (854001/7812500000 : ℝ)*(sp_s1_22) + (526529985209/500000000000 : ℝ)*(f.failure) + (1676040561061/1000000000000 : ℝ)*(f.sum) + (617861964272227477/6549471050000000000000000000000 : ℝ)*base63 + (98265893172677/115592500000000000000000000 : ℝ)*base64 + (214468934198393/424950000000000000000000000 : ℝ)*base67 + (536236125931933/462370000000000000000000000 : ℝ)*base69 + (7483944020271408089/67480589650000000000000000000000 : ℝ)*base70 + (13234993192103/22803906250000000000000000 : ℝ)*base73 + (140909275930171/141650000000000000000000000 : ℝ)*base75 + (336761572121891/729725000000000000000000000 : ℝ)*base76 + (32745484061389/9923092440000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (12401/50000000000000000 : ℝ)*base86 + (12401/50000000000000000 : ℝ)*base88 + (12401/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(83413/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(83413/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (968812525060693317720674962273/61849929860675000000000000000000000 : ℝ) := by norm_num
    linear_combination (754204203993/1000000000000 : ℝ)*(base7) + (1730037/250000000000 : ℝ)*(base15) + (50683404753/1000000000000 : ℝ)*(base40) + (101917483561/125000000000 : ℝ)*(base43) + (479463/200000000000 : ℝ)*(base50) + (1712188029283/1000000000000 : ℝ)*(major_s1_0) + (179369632159/200000000000 : ℝ)*(major_s1_1) + (1712188029283/1000000000000 : ℝ)*(major_s1_2) + (4072647/100000000000 : ℝ)*(sp_s1_2) + (74964369/500000000000 : ℝ)*(sp_s1_7) + (65815115601/62500000000 : ℝ)*(sp_s1_21) + (934262363347/500000000000 : ℝ)*(sp_s1_22) + (1053151051883/1000000000000 : ℝ)*(sp_s1_23) + (923390502071/500000000000 : ℝ)*(sp_s1_27) + (21851536003/20000000000 : ℝ)*(f.failure) + (934265823421/500000000000 : ℝ)*(f.sum) + (278438017549869549/1309894210000000000000000000000 : ℝ)*base63 + (400835288629/462370000000000000000000000 : ℝ)*base65 + (708500889349721/1869780000000000000000000000 : ℝ)*base67 + (58856537023317/462370000000000000000000000 : ℝ)*base69 + (317385006260701081/992361612500000000000000000000 : ℝ)*base70 + (61169587907017/85850000000000000000000000 : ℝ)*base73 + (3654235912903/5666000000000000000000000 : ℝ)*base75 + (74746757111877/85850000000000000000000000 : ℝ)*base76 + (6636896358190695451/16052061300000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (133/2000000000000000 : ℝ)*base87 + (133/2000000000000000 : ℝ)*base89 + (133/2000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((87567/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(87567/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-93489/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-93489/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(46237/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(46237/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((35467/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(35467/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-16891/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-16891/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(83413/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(83413/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c308086_s1 p hpa hpb X hX hprev0

#print axioms solution

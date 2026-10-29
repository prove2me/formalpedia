-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c305086_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:34:09.514085+00:00
-- url     : https://prove2.me/submissions/a27956c9-f77b-431e-8dcc-dc79924a8849

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
theorem collision_support_c305086_s1_s1_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (205042291/312500000 : ℝ)*x 0 + (1570686421/5000000000 : ℝ)*x 1 + (3011531403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (205042291/312500000 : ℝ)^67 ≤ (11497663443251/20000000000000 : ℝ)^51 := by
    have hnat : (205042291 : ℕ)^67*20000000000000^51 ≤ 11497663443251^51*312500000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205042291 312500000 11497663443251 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1570686421/5000000000 : ℝ)^67 ≤ (4369010056471/20000000000000 : ℝ)^51 := by
    have hnat : (1570686421 : ℕ)^67*20000000000000^51 ≤ 4369010056471^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1570686421 5000000000 4369010056471 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3011531403/10000000000 : ℝ)^67 ≤ (20666632488089/100000000000000 : ℝ)^51 := by
    have hnat : (3011531403 : ℕ)^67*100000000000000^51 ≤ 20666632488089^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3011531403 10000000000 20666632488089 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(205042291/312500000 : ℝ), (1570686421/5000000000 : ℝ), (3011531403/10000000000 : ℝ)] ![(11497663443251/20000000000000 : ℝ), (4369010056471/20000000000000 : ℝ), (20666632488089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(205042291/312500000 : ℝ)|^67 ≤ (11497663443251/20000000000000 : ℝ)^51
        have hw : |(205042291/312500000 : ℝ)|=(205042291/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1570686421/5000000000 : ℝ)|^67 ≤ (4369010056471/20000000000000 : ℝ)^51
        have hw : |(1570686421/5000000000 : ℝ)|=(1570686421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3011531403/10000000000 : ℝ)|^67 ≤ (20666632488089/100000000000000 : ℝ)^51
        have hw : |(3011531403/10000000000 : ℝ)|=(3011531403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305086_s1_s1_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6218889607/10000000000 : ℝ)*x 0 + (-3422945429/10000000000 : ℝ)*x 1 + (-3154829609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6218889607/10000000000 : ℝ)^67 ≤ (53579087093359/100000000000000 : ℝ)^51 := by
    have hnat : (6218889607 : ℕ)^67*100000000000000^51 ≤ 53579087093359^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6218889607 10000000000 53579087093359 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3422945429/10000000000 : ℝ)^67 ≤ (24452844122293/100000000000000 : ℝ)^51 := by
    have hnat : (3422945429 : ℕ)^67*100000000000000^51 ≤ 24452844122293^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3422945429 10000000000 24452844122293 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3154829609/10000000000 : ℝ)^67 ≤ (2196806876527/10000000000000 : ℝ)^51 := by
    have hnat : (3154829609 : ℕ)^67*10000000000000^51 ≤ 2196806876527^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3154829609 10000000000 2196806876527 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6218889607/10000000000 : ℝ), (-3422945429/10000000000 : ℝ), (-3154829609/10000000000 : ℝ)] ![(53579087093359/100000000000000 : ℝ), (24452844122293/100000000000000 : ℝ), (2196806876527/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6218889607/10000000000 : ℝ)|^67 ≤ (53579087093359/100000000000000 : ℝ)^51
        have hw : |(6218889607/10000000000 : ℝ)|=(6218889607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3422945429/10000000000 : ℝ)|^67 ≤ (24452844122293/100000000000000 : ℝ)^51
        have hw : |(-3422945429/10000000000 : ℝ)|=(3422945429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3154829609/10000000000 : ℝ)|^67 ≤ (2196806876527/10000000000000 : ℝ)^51
        have hw : |(-3154829609/10000000000 : ℝ)|=(3154829609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305086_s1_s1_6 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (450285029/1250000000 : ℝ)*x 0 + (-2478101171/10000000000 : ℝ)*x 1 + (6593048951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (450285029/1250000000 : ℝ)^67 ≤ (1045982800651/4000000000000 : ℝ)^51 := by
    have hnat : (450285029 : ℕ)^67*4000000000000^51 ≤ 1045982800651^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450285029 1250000000 1045982800651 4000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2478101171/10000000000 : ℝ)^67 ≤ (7998503401871/50000000000000 : ℝ)^51 := by
    have hnat : (2478101171 : ℕ)^67*50000000000000^51 ≤ 7998503401871^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2478101171 10000000000 7998503401871 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6593048951/10000000000 : ℝ)^67 ≤ (2892671158289/5000000000000 : ℝ)^51 := by
    have hnat : (6593048951 : ℕ)^67*5000000000000^51 ≤ 2892671158289^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6593048951 10000000000 2892671158289 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(450285029/1250000000 : ℝ), (-2478101171/10000000000 : ℝ), (6593048951/10000000000 : ℝ)] ![(1045982800651/4000000000000 : ℝ), (7998503401871/50000000000000 : ℝ), (2892671158289/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(450285029/1250000000 : ℝ)|^67 ≤ (1045982800651/4000000000000 : ℝ)^51
        have hw : |(450285029/1250000000 : ℝ)|=(450285029/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2478101171/10000000000 : ℝ)|^67 ≤ (7998503401871/50000000000000 : ℝ)^51
        have hw : |(-2478101171/10000000000 : ℝ)|=(2478101171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6593048951/10000000000 : ℝ)|^67 ≤ (2892671158289/5000000000000 : ℝ)^51
        have hw : |(6593048951/10000000000 : ℝ)|=(6593048951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305086_s1_s1_7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (60094509/5000000000 : ℝ)*x 0 + (-1680688277/2000000000 : ℝ)*x 1 + (2951628471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (60094509/5000000000 : ℝ)^67 ≤ (150120302247/50000000000000 : ℝ)^51 := by
    have hnat : (60094509 : ℕ)^67*50000000000000^51 ≤ 150120302247^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60094509 5000000000 150120302247 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1680688277/2000000000 : ℝ)^67 ≤ (79571485415433/100000000000000 : ℝ)^51 := by
    have hnat : (1680688277 : ℕ)^67*100000000000000^51 ≤ 79571485415433^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1680688277 2000000000 79571485415433 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2951628471/10000000000 : ℝ)^67 ≤ (20128273967531/100000000000000 : ℝ)^51 := by
    have hnat : (2951628471 : ℕ)^67*100000000000000^51 ≤ 20128273967531^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2951628471 10000000000 20128273967531 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(60094509/5000000000 : ℝ), (-1680688277/2000000000 : ℝ), (2951628471/10000000000 : ℝ)] ![(150120302247/50000000000000 : ℝ), (79571485415433/100000000000000 : ℝ), (20128273967531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(60094509/5000000000 : ℝ)|^67 ≤ (150120302247/50000000000000 : ℝ)^51
        have hw : |(60094509/5000000000 : ℝ)|=(60094509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1680688277/2000000000 : ℝ)|^67 ≤ (79571485415433/100000000000000 : ℝ)^51
        have hw : |(-1680688277/2000000000 : ℝ)|=(1680688277/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2951628471/10000000000 : ℝ)|^67 ≤ (20128273967531/100000000000000 : ℝ)^51
        have hw : |(2951628471/10000000000 : ℝ)|=(2951628471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305086_s1_s1_8 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (896545631/2500000000 : ℝ)*x 0 + (6759894699/10000000000 : ℝ)*x 1 + (17699851/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (896545631/2500000000 : ℝ)^67 ≤ (6499040250611/25000000000000 : ℝ)^51 := by
    have hnat : (896545631 : ℕ)^67*25000000000000^51 ≤ 6499040250611^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896545631 2500000000 6499040250611 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6759894699/10000000000 : ℝ)^67 ≤ (1868261972171/3125000000000 : ℝ)^51 := by
    have hnat : (6759894699 : ℕ)^67*3125000000000^51 ≤ 1868261972171^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6759894699 10000000000 1868261972171 3125000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17699851/78125000 : ℝ)^67 ≤ (888715991859/6250000000000 : ℝ)^51 := by
    have hnat : (17699851 : ℕ)^67*6250000000000^51 ≤ 888715991859^51*78125000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17699851 78125000 888715991859 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(896545631/2500000000 : ℝ), (6759894699/10000000000 : ℝ), (17699851/78125000 : ℝ)] ![(6499040250611/25000000000000 : ℝ), (1868261972171/3125000000000 : ℝ), (888715991859/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(896545631/2500000000 : ℝ)|^67 ≤ (6499040250611/25000000000000 : ℝ)^51
        have hw : |(896545631/2500000000 : ℝ)|=(896545631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6759894699/10000000000 : ℝ)|^67 ≤ (1868261972171/3125000000000 : ℝ)^51
        have hw : |(6759894699/10000000000 : ℝ)|=(6759894699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(17699851/78125000 : ℝ)|^67 ≤ (888715991859/6250000000000 : ℝ)^51
        have hw : |(17699851/78125000 : ℝ)|=(17699851/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305086_s1_s1_9 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4635465923/5000000000 : ℝ)*x 0 + (-3837867/156250000 : ℝ)*x 1 + (-1558546023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4635465923/5000000000 : ℝ)^67 ≤ (45266734047661/50000000000000 : ℝ)^51 := by
    have hnat : (4635465923 : ℕ)^67*50000000000000^51 ≤ 45266734047661^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4635465923 5000000000 45266734047661 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3837867/156250000 : ℝ)^67 ≤ (767814886147/100000000000000 : ℝ)^51 := by
    have hnat : (3837867 : ℕ)^67*100000000000000^51 ≤ 767814886147^51*156250000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3837867 156250000 767814886147 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1558546023/10000000000 : ℝ)^67 ≤ (8698716998699/100000000000000 : ℝ)^51 := by
    have hnat : (1558546023 : ℕ)^67*100000000000000^51 ≤ 8698716998699^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1558546023 10000000000 8698716998699 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4635465923/5000000000 : ℝ), (-3837867/156250000 : ℝ), (-1558546023/10000000000 : ℝ)] ![(45266734047661/50000000000000 : ℝ), (767814886147/100000000000000 : ℝ), (8698716998699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4635465923/5000000000 : ℝ)|^67 ≤ (45266734047661/50000000000000 : ℝ)^51
        have hw : |(4635465923/5000000000 : ℝ)|=(4635465923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3837867/156250000 : ℝ)|^67 ≤ (767814886147/100000000000000 : ℝ)^51
        have hw : |(-3837867/156250000 : ℝ)|=(3837867/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1558546023/10000000000 : ℝ)|^67 ≤ (8698716998699/100000000000000 : ℝ)^51
        have hw : |(-1558546023/10000000000 : ℝ)|=(1558546023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305086_s1_s1_13 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (914567917/2500000000 : ℝ)*x 0 + (-1394271713/10000000000 : ℝ)*x 1 + (3635861709/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (914567917/2500000000 : ℝ)^67 ≤ (26684832929027/100000000000000 : ℝ)^51 := by
    have hnat : (914567917 : ℕ)^67*100000000000000^51 ≤ 26684832929027^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914567917 2500000000 26684832929027 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1394271713/10000000000 : ℝ)^67 ≤ (1878656584317/25000000000000 : ℝ)^51 := by
    have hnat : (1394271713 : ℕ)^67*25000000000000^51 ≤ 1878656584317^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1394271713 10000000000 1878656584317 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3635861709/5000000000 : ℝ)^67 ≤ (16450135179421/25000000000000 : ℝ)^51 := by
    have hnat : (3635861709 : ℕ)^67*25000000000000^51 ≤ 16450135179421^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3635861709 5000000000 16450135179421 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(914567917/2500000000 : ℝ), (-1394271713/10000000000 : ℝ), (3635861709/5000000000 : ℝ)] ![(26684832929027/100000000000000 : ℝ), (1878656584317/25000000000000 : ℝ), (16450135179421/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(914567917/2500000000 : ℝ)|^67 ≤ (26684832929027/100000000000000 : ℝ)^51
        have hw : |(914567917/2500000000 : ℝ)|=(914567917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1394271713/10000000000 : ℝ)|^67 ≤ (1878656584317/25000000000000 : ℝ)^51
        have hw : |(-1394271713/10000000000 : ℝ)|=(1394271713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3635861709/5000000000 : ℝ)|^67 ≤ (16450135179421/25000000000000 : ℝ)^51
        have hw : |(3635861709/5000000000 : ℝ)|=(3635861709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305086_s1_s1_14 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-793/10000000000 : ℝ)*x 0 + (-3855537871/10000000000 : ℝ)*x 1 + (7738871577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (793/10000000000 : ℝ)^67 ≤ (23473/50000000000000 : ℝ)^51 := by
    have hnat : (793 : ℕ)^67*50000000000000^51 ≤ 23473^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      793 10000000000 23473 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3855537871/10000000000 : ℝ)^67 ≤ (14295497800259/50000000000000 : ℝ)^51 := by
    have hnat : (3855537871 : ℕ)^67*50000000000000^51 ≤ 14295497800259^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3855537871 10000000000 14295497800259 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7738871577/10000000000 : ℝ)^67 ≤ (71409004349441/100000000000000 : ℝ)^51 := by
    have hnat : (7738871577 : ℕ)^67*100000000000000^51 ≤ 71409004349441^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7738871577 10000000000 71409004349441 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-793/10000000000 : ℝ), (-3855537871/10000000000 : ℝ), (7738871577/10000000000 : ℝ)] ![(23473/50000000000000 : ℝ), (14295497800259/50000000000000 : ℝ), (71409004349441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-793/10000000000 : ℝ)|^67 ≤ (23473/50000000000000 : ℝ)^51
        have hw : |(-793/10000000000 : ℝ)|=(793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3855537871/10000000000 : ℝ)|^67 ≤ (14295497800259/50000000000000 : ℝ)^51
        have hw : |(-3855537871/10000000000 : ℝ)|=(3855537871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7738871577/10000000000 : ℝ)|^67 ≤ (71409004349441/100000000000000 : ℝ)^51
        have hw : |(7738871577/10000000000 : ℝ)|=(7738871577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305086_s1_s1_15 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (86834343/100000000 : ℝ)*x 0 + (445545297/2000000000 : ℝ)*x 1 + (69648903/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86834343/100000000 : ℝ)^67 ≤ (5192033763071/6250000000000 : ℝ)^51 := by
    have hnat : (86834343 : ℕ)^67*6250000000000^51 ≤ 5192033763071^51*100000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86834343 100000000 5192033763071 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (445545297/2000000000 : ℝ)^67 ≤ (2781630942189/20000000000000 : ℝ)^51 := by
    have hnat : (445545297 : ℕ)^67*20000000000000^51 ≤ 2781630942189^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445545297 2000000000 2781630942189 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (69648903/1000000000 : ℝ)^67 ≤ (377413133461/12500000000000 : ℝ)^51 := by
    have hnat : (69648903 : ℕ)^67*12500000000000^51 ≤ 377413133461^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69648903 1000000000 377413133461 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(86834343/100000000 : ℝ), (445545297/2000000000 : ℝ), (69648903/1000000000 : ℝ)] ![(5192033763071/6250000000000 : ℝ), (2781630942189/20000000000000 : ℝ), (377413133461/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(86834343/100000000 : ℝ)|^67 ≤ (5192033763071/6250000000000 : ℝ)^51
        have hw : |(86834343/100000000 : ℝ)|=(86834343/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(445545297/2000000000 : ℝ)|^67 ≤ (2781630942189/20000000000000 : ℝ)^51
        have hw : |(445545297/2000000000 : ℝ)|=(445545297/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(69648903/1000000000 : ℝ)|^67 ≤ (377413133461/12500000000000 : ℝ)^51
        have hw : |(69648903/1000000000 : ℝ)|=(69648903/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305086_s1_s1_16 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8070410981/10000000000 : ℝ)*x 0 + (-1996124671/10000000000 : ℝ)*x 1 + (-2054488939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8070410981/10000000000 : ℝ)^67 ≤ (75454725603379/100000000000000 : ℝ)^51 := by
    have hnat : (8070410981 : ℕ)^67*100000000000000^51 ≤ 75454725603379^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8070410981 10000000000 75454725603379 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1996124671/10000000000 : ℝ)^67 ≤ (3010084603257/25000000000000 : ℝ)^51 := by
    have hnat : (1996124671 : ℕ)^67*25000000000000^51 ≤ 3010084603257^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1996124671 10000000000 3010084603257 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2054488939/10000000000 : ℝ)^67 ≤ (12504935975751/100000000000000 : ℝ)^51 := by
    have hnat : (2054488939 : ℕ)^67*100000000000000^51 ≤ 12504935975751^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2054488939 10000000000 12504935975751 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8070410981/10000000000 : ℝ), (-1996124671/10000000000 : ℝ), (-2054488939/10000000000 : ℝ)] ![(75454725603379/100000000000000 : ℝ), (3010084603257/25000000000000 : ℝ), (12504935975751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8070410981/10000000000 : ℝ)|^67 ≤ (75454725603379/100000000000000 : ℝ)^51
        have hw : |(8070410981/10000000000 : ℝ)|=(8070410981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1996124671/10000000000 : ℝ)|^67 ≤ (3010084603257/25000000000000 : ℝ)^51
        have hw : |(-1996124671/10000000000 : ℝ)|=(1996124671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2054488939/10000000000 : ℝ)|^67 ≤ (12504935975751/100000000000000 : ℝ)^51
        have hw : |(-2054488939/10000000000 : ℝ)|=(2054488939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305086_s1_s1_20 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (224019109/1000000000 : ℝ)*x 0 + (-1338459929/10000000000 : ℝ)*x 1 + (65209331/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (224019109/1000000000 : ℝ)^67 ≤ (7005238625227/50000000000000 : ℝ)^51 := by
    have hnat : (224019109 : ℕ)^67*50000000000000^51 ≤ 7005238625227^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224019109 1000000000 7005238625227 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1338459929/10000000000 : ℝ)^67 ≤ (7121954856213/100000000000000 : ℝ)^51 := by
    have hnat : (1338459929 : ℕ)^67*100000000000000^51 ≤ 7121954856213^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338459929 10000000000 7121954856213 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65209331/78125000 : ℝ)^67 ≤ (39433783939551/50000000000000 : ℝ)^51 := by
    have hnat : (65209331 : ℕ)^67*50000000000000^51 ≤ 39433783939551^51*78125000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65209331 78125000 39433783939551 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(224019109/1000000000 : ℝ), (-1338459929/10000000000 : ℝ), (65209331/78125000 : ℝ)] ![(7005238625227/50000000000000 : ℝ), (7121954856213/100000000000000 : ℝ), (39433783939551/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(224019109/1000000000 : ℝ)|^67 ≤ (7005238625227/50000000000000 : ℝ)^51
        have hw : |(224019109/1000000000 : ℝ)|=(224019109/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1338459929/10000000000 : ℝ)|^67 ≤ (7121954856213/100000000000000 : ℝ)^51
        have hw : |(-1338459929/10000000000 : ℝ)|=(1338459929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65209331/78125000 : ℝ)|^67 ≤ (39433783939551/50000000000000 : ℝ)^51
        have hw : |(65209331/78125000 : ℝ)|=(65209331/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305086_s1_s1_21 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1292983/500000000 : ℝ)*x 0 + (-4317103243/5000000000 : ℝ)*x 1 + (1327037121/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1292983/500000000 : ℝ)^67 ≤ (39892994163/100000000000000 : ℝ)^51 := by
    have hnat : (1292983 : ℕ)^67*100000000000000^51 ≤ 39892994163^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292983 500000000 39892994163 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4317103243/5000000000 : ℝ)^67 ≤ (4122719482849/5000000000000 : ℝ)^51 := by
    have hnat : (4317103243 : ℕ)^67*5000000000000^51 ≤ 4122719482849^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317103243 5000000000 4122719482849 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1327037121/5000000000 : ℝ)^67 ≤ (8752858669811/50000000000000 : ℝ)^51 := by
    have hnat : (1327037121 : ℕ)^67*50000000000000^51 ≤ 8752858669811^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327037121 5000000000 8752858669811 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1292983/500000000 : ℝ), (-4317103243/5000000000 : ℝ), (1327037121/5000000000 : ℝ)] ![(39892994163/100000000000000 : ℝ), (4122719482849/5000000000000 : ℝ), (8752858669811/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1292983/500000000 : ℝ)|^67 ≤ (39892994163/100000000000000 : ℝ)^51
        have hw : |(1292983/500000000 : ℝ)|=(1292983/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4317103243/5000000000 : ℝ)|^67 ≤ (4122719482849/5000000000000 : ℝ)^51
        have hw : |(-4317103243/5000000000 : ℝ)|=(4317103243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1327037121/5000000000 : ℝ)|^67 ≤ (8752858669811/50000000000000 : ℝ)^51
        have hw : |(1327037121/5000000000 : ℝ)|=(1327037121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305086_s1_s1_22 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2208278739/2500000000 : ℝ)*x 0 + (1270473259/10000000000 : ℝ)*x 1 + (23692981/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2208278739/2500000000 : ℝ)^67 ≤ (16991762513599/20000000000000 : ℝ)^51 := by
    have hnat : (2208278739 : ℕ)^67*20000000000000^51 ≤ 16991762513599^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2208278739 2500000000 16991762513599 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1270473259/10000000000 : ℝ)^67 ≤ (6650536396883/100000000000000 : ℝ)^51 := by
    have hnat : (1270473259 : ℕ)^67*100000000000000^51 ≤ 6650536396883^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1270473259 10000000000 6650536396883 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (23692981/156250000 : ℝ)^67 ≤ (8390651014831/100000000000000 : ℝ)^51 := by
    have hnat : (23692981 : ℕ)^67*100000000000000^51 ≤ 8390651014831^51*156250000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23692981 156250000 8390651014831 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2208278739/2500000000 : ℝ), (1270473259/10000000000 : ℝ), (23692981/156250000 : ℝ)] ![(16991762513599/20000000000000 : ℝ), (6650536396883/100000000000000 : ℝ), (8390651014831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2208278739/2500000000 : ℝ)|^67 ≤ (16991762513599/20000000000000 : ℝ)^51
        have hw : |(2208278739/2500000000 : ℝ)|=(2208278739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1270473259/10000000000 : ℝ)|^67 ≤ (6650536396883/100000000000000 : ℝ)^51
        have hw : |(1270473259/10000000000 : ℝ)|=(1270473259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(23692981/156250000 : ℝ)|^67 ≤ (8390651014831/100000000000000 : ℝ)^51
        have hw : |(23692981/156250000 : ℝ)|=(23692981/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305086_s1_s1_23 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4772758549/10000000000 : ℝ)*x 0 + (-1530648997/5000000000 : ℝ)*x 1 + (-126915923/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4772758549/10000000000 : ℝ)^67 ≤ (37843496610803/100000000000000 : ℝ)^51 := by
    have hnat : (4772758549 : ℕ)^67*100000000000000^51 ≤ 37843496610803^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4772758549 10000000000 37843496610803 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1530648997/5000000000 : ℝ)^67 ≤ (21116458898519/100000000000000 : ℝ)^51 := by
    have hnat : (1530648997 : ℕ)^67*100000000000000^51 ≤ 21116458898519^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1530648997 5000000000 21116458898519 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (126915923/250000000 : ℝ)^67 ≤ (20520022236441/50000000000000 : ℝ)^51 := by
    have hnat : (126915923 : ℕ)^67*50000000000000^51 ≤ 20520022236441^51*250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126915923 250000000 20520022236441 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4772758549/10000000000 : ℝ), (-1530648997/5000000000 : ℝ), (-126915923/250000000 : ℝ)] ![(37843496610803/100000000000000 : ℝ), (21116458898519/100000000000000 : ℝ), (20520022236441/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4772758549/10000000000 : ℝ)|^67 ≤ (37843496610803/100000000000000 : ℝ)^51
        have hw : |(4772758549/10000000000 : ℝ)|=(4772758549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1530648997/5000000000 : ℝ)|^67 ≤ (21116458898519/100000000000000 : ℝ)^51
        have hw : |(-1530648997/5000000000 : ℝ)|=(1530648997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-126915923/250000000 : ℝ)|^67 ≤ (20520022236441/50000000000000 : ℝ)^51
        have hw : |(-126915923/250000000 : ℝ)|=(126915923/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305086_s1_s1_27 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (376825101/500000000 : ℝ)*x 0 + (-888220621/10000000000 : ℝ)*x 1 + (3678445267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (376825101/500000000 : ℝ)^67 ≤ (68965971988487/100000000000000 : ℝ)^51 := by
    have hnat : (376825101 : ℕ)^67*100000000000000^51 ≤ 68965971988487^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      376825101 500000000 68965971988487 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (888220621/10000000000 : ℝ)^67 ≤ (4155708152681/100000000000000 : ℝ)^51 := by
    have hnat : (888220621 : ℕ)^67*100000000000000^51 ≤ 4155708152681^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      888220621 10000000000 4155708152681 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3678445267/10000000000 : ℝ)^67 ≤ (13439159918529/50000000000000 : ℝ)^51 := by
    have hnat : (3678445267 : ℕ)^67*50000000000000^51 ≤ 13439159918529^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3678445267 10000000000 13439159918529 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(376825101/500000000 : ℝ), (-888220621/10000000000 : ℝ), (3678445267/10000000000 : ℝ)] ![(68965971988487/100000000000000 : ℝ), (4155708152681/100000000000000 : ℝ), (13439159918529/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(376825101/500000000 : ℝ)|^67 ≤ (68965971988487/100000000000000 : ℝ)^51
        have hw : |(376825101/500000000 : ℝ)|=(376825101/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-888220621/10000000000 : ℝ)|^67 ≤ (4155708152681/100000000000000 : ℝ)^51
        have hw : |(-888220621/10000000000 : ℝ)|=(888220621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3678445267/10000000000 : ℝ)|^67 ≤ (13439159918529/50000000000000 : ℝ)^51
        have hw : |(3678445267/10000000000 : ℝ)|=(3678445267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c305086_s1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((18453/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18453/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-96369/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-96369/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(95061/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(95061/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((40551/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(40551/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-11353/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-11353/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(89257/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(89257/100000 : ℝ)*X 1 2) := by
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
  have main1 : (76771/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76771/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (93447/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s1_pow0 : (18453/20000 : ℝ) ^ (133/32 : ℝ) ≤ (35781206281971689119/50000000000000000000 : ℝ) := by
    have hpowers : (18453/20000 : ℝ)^133 ≤ (35781206281971689119/50000000000000000000 : ℝ)^32 := by
      have hnat : (18453 : ℕ)^133*50000000000000000000^32 ≤ 35781206281971689119^32*20000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18453 20000 35781206281971689119 50000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18453/20000 : ℝ)) (X := (35781206281971689119/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (85781206281971689119/50000000000000000000 : ℝ) ≤ (711676028884651/625000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (85781206281971689119/50000000000000000000 : ℝ)^32 ≤ (711676028884651/625000000000000 : ℝ)^133 := by
      have hnat : (85781206281971689119 : ℕ)^32*625000000000000^133 ≤ 711676028884651^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        85781206281971689119 50000000000000000000 711676028884651 625000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (711676028884651/625000000000000 : ℝ)) (X := (85781206281971689119/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (60781206281971689119/25000000000000000000 : ℝ) ≤ (3095787340485219/2500000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (60781206281971689119/25000000000000000000 : ℝ)^32 ≤ (3095787340485219/2500000000000000 : ℝ)^133 := by
      have hnat : (60781206281971689119 : ℕ)^32*2500000000000000^133 ≤ 3095787340485219^133*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60781206281971689119 25000000000000000000 3095787340485219 2500000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3095787340485219/2500000000000000 : ℝ)) (X := (60781206281971689119/25000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(28892009628217/192218750000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(49816644989323/461325000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (18453/20000 : ℝ)) (alpha := (28892009628217/192218750000000 : ℝ)) (beta := (49816644989323/461325000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (18453/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(28892009628217/192218750000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(49816644989323/461325000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (96369/100000 : ℝ) ^ (133/32 : ℝ) ≤ (3430043377858584891/4000000000000000000 : ℝ) := by
    have hpowers : (96369/100000 : ℝ)^133 ≤ (3430043377858584891/4000000000000000000 : ℝ)^32 := by
      have hnat : (96369 : ℕ)^133*4000000000000000000^32 ≤ 3430043377858584891^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        96369 100000 3430043377858584891 4000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (96369/100000 : ℝ)) (X := (3430043377858584891/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (7430043377858584891/4000000000000000000 : ℝ) ≤ (11606607258082181/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (7430043377858584891/4000000000000000000 : ℝ)^32 ≤ (11606607258082181/10000000000000000 : ℝ)^133 := by
      have hnat : (7430043377858584891 : ℕ)^32*10000000000000000^133 ≤ 11606607258082181^133*4000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7430043377858584891 4000000000000000000 11606607258082181 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11606607258082181/10000000000000000 : ℝ)) (X := (7430043377858584891/4000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (5430043377858584891/2000000000000000000 : ℝ) ≤ (2543293637067587/2000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (5430043377858584891/2000000000000000000 : ℝ)^32 ≤ (2543293637067587/2000000000000000 : ℝ)^133 := by
      have hnat : (5430043377858584891 : ℕ)^32*2000000000000000^133 ≤ 2543293637067587^133*2000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5430043377858584891 2000000000000000000 2543293637067587 2000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2543293637067587/2000000000000000 : ℝ)) (X := (5430043377858584891/2000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1606607258082181/9636900000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(554930463627877/4818450000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (96369/100000 : ℝ)) (alpha := (1606607258082181/9636900000000000 : ℝ)) (beta := (554930463627877/4818450000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (96369/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1606607258082181/9636900000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(554930463627877/4818450000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (95061/100000 : ℝ) ^ (133/32 : ℝ) ≤ (81016296415178002323/100000000000000000000 : ℝ) := by
    have hpowers : (95061/100000 : ℝ)^133 ≤ (81016296415178002323/100000000000000000000 : ℝ)^32 := by
      have hnat : (95061 : ℕ)^133*100000000000000000000^32 ≤ 81016296415178002323^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        95061 100000 81016296415178002323 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (95061/100000 : ℝ)) (X := (81016296415178002323/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (181016296415178002323/100000000000000000000 : ℝ) ≤ (11534725403951441/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (181016296415178002323/100000000000000000000 : ℝ)^32 ≤ (11534725403951441/10000000000000000 : ℝ)^133 := by
      have hnat : (181016296415178002323 : ℕ)^32*10000000000000000^133 ≤ 11534725403951441^133*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        181016296415178002323 100000000000000000000 11534725403951441 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11534725403951441/10000000000000000 : ℝ)) (X := (181016296415178002323/100000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (131016296415178002323/50000000000000000000 : ℝ) ≤ (1260831114545689/1000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (131016296415178002323/50000000000000000000 : ℝ)^32 ≤ (1260831114545689/1000000000000000 : ℝ)^133 := by
      have hnat : (131016296415178002323 : ℕ)^32*1000000000000000^133 ≤ 1260831114545689^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        131016296415178002323 50000000000000000000 1260831114545689 1000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1260831114545689/1000000000000000 : ℝ)) (X := (131016296415178002323/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1534725403951441/9506100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1073585741505449/9506100000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (95061/100000 : ℝ)) (alpha := (1534725403951441/9506100000000000 : ℝ)) (beta := (1073585741505449/9506100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (95061/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1534725403951441/9506100000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1073585741505449/9506100000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_1 : ((205042291/312500000 : ℝ)*X 1 0+(1570686421/5000000000 : ℝ)*X 1 1+(3011531403/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305086_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((6218889607/10000000000 : ℝ)*X 2 0+(-3422945429/10000000000 : ℝ)*X 2 1+(-3154829609/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305086_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((450285029/1250000000 : ℝ)*X 0 0+(-2478101171/10000000000 : ℝ)*X 0 1+(6593048951/10000000000 : ℝ)*X 0 2+(450285029/1250000000 : ℝ)*X 1 0+(-2478101171/10000000000 : ℝ)*X 1 1+(6593048951/10000000000 : ℝ)*X 1 2+(450285029/1250000000 : ℝ)*X 2 0+(-2478101171/10000000000 : ℝ)*X 2 1+(6593048951/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305086_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((60094509/5000000000 : ℝ)*X 0 0+(-1680688277/2000000000 : ℝ)*X 0 1+(2951628471/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305086_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((896545631/2500000000 : ℝ)*X 1 0+(6759894699/10000000000 : ℝ)*X 1 1+(17699851/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305086_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((4635465923/5000000000 : ℝ)*X 2 0+(-3837867/156250000 : ℝ)*X 2 1+(-1558546023/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305086_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((914567917/2500000000 : ℝ)*X 0 0+(-1394271713/10000000000 : ℝ)*X 0 1+(3635861709/5000000000 : ℝ)*X 0 2+(914567917/2500000000 : ℝ)*X 1 0+(-1394271713/10000000000 : ℝ)*X 1 1+(3635861709/5000000000 : ℝ)*X 1 2+(914567917/2500000000 : ℝ)*X 2 0+(-1394271713/10000000000 : ℝ)*X 2 1+(3635861709/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305086_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-793/10000000000 : ℝ)*X 0 0+(-3855537871/10000000000 : ℝ)*X 0 1+(7738871577/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305086_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((86834343/100000000 : ℝ)*X 1 0+(445545297/2000000000 : ℝ)*X 1 1+(69648903/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305086_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((8070410981/10000000000 : ℝ)*X 2 0+(-1996124671/10000000000 : ℝ)*X 2 1+(-2054488939/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305086_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((224019109/1000000000 : ℝ)*X 0 0+(-1338459929/10000000000 : ℝ)*X 0 1+(65209331/78125000 : ℝ)*X 0 2+(224019109/1000000000 : ℝ)*X 1 0+(-1338459929/10000000000 : ℝ)*X 1 1+(65209331/78125000 : ℝ)*X 1 2+(224019109/1000000000 : ℝ)*X 2 0+(-1338459929/10000000000 : ℝ)*X 2 1+(65209331/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305086_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((1292983/500000000 : ℝ)*X 0 0+(-4317103243/5000000000 : ℝ)*X 0 1+(1327037121/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305086_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((2208278739/2500000000 : ℝ)*X 1 0+(1270473259/10000000000 : ℝ)*X 1 1+(23692981/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305086_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((4772758549/10000000000 : ℝ)*X 2 0+(-1530648997/5000000000 : ℝ)*X 2 1+(-126915923/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305086_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((376825101/500000000 : ℝ)*X 0 0+(-888220621/10000000000 : ℝ)*X 0 1+(3678445267/10000000000 : ℝ)*X 0 2+(376825101/500000000 : ℝ)*X 1 0+(-888220621/10000000000 : ℝ)*X 1 1+(3678445267/10000000000 : ℝ)*X 1 2+(376825101/500000000 : ℝ)*X 2 0+(-888220621/10000000000 : ℝ)*X 2 1+(3678445267/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305086_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((40551/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(40551/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (14491039410419885691985505419/3440103908050000000000000000000000 : ℝ) := by norm_num
    linear_combination (506958171191/1000000000000 : ℝ)*(base7) + (253934733541/1000000000000 : ℝ)*(base43) + (424678145291/500000000000 : ℝ)*(base54) + (1026759/1000000000000 : ℝ)*(base60) + (1614633326157/1000000000000 : ℝ)*(major_s1_0) + (1360698592617/1000000000000 : ℝ)*(major_s1_1) + (30611081423/40000000000 : ℝ)*(major_s1_2) + (4179633/250000000000 : ℝ)*(sp_s1_6) + (100230521753/62500000000 : ℝ)*(sp_s1_7) + (1857627694181/1000000000000 : ℝ)*(sp_s1_8) + (75429746737/100000000000 : ℝ)*(sp_s1_9) + (713397914587/1000000000000 : ℝ)*(sp_s1_13) + (39202689/1000000000000 : ℝ)*(sp_s1_16) + (288287/62500000000 : ℝ)*(sp_s1_21) + (1055812752509/1000000000000 : ℝ)*(f.failure) + (1857627694181/1000000000000 : ℝ)*(f.sum) + (569762781131153519/3355653300000000000000000000000 : ℝ)*base62 + (288977671316569/380244000000000000000000000 : ℝ)*base64 + (13303576910951/35300000000000000000000000 : ℝ)*base66 + (681248874610133/1901220000000000000000000000 : ℝ)*base68 + (108240707055397328419/292360105500000000000000000000000 : ℝ)*base71 + (44009935239089/76887500000000000000000000 : ℝ)*base72 + (4036594816013/4412500000000000000000000 : ℝ)*base74 + (239366665703199/768875000000000000000000000 : ℝ)*base76 + (74268614766261367/217130300000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (57/1562500000000000 : ℝ)*base86 + (3239/3125000000000000 : ℝ)*base88 + (57/1562500000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-11353/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-11353/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2691809346269872336190898427357/195655909770343750000000000000000000 : ℝ) := by norm_num
    linear_combination (185698809167/200000000000 : ℝ)*(base7) + (7331178359/20000000000 : ℝ)*(base33) + (826383/250000000000 : ℝ)*(base40) + (1231905637759/1000000000000 : ℝ)*(major_s1_0) + (399616138927/250000000000 : ℝ)*(major_s1_1) + (399616138927/250000000000 : ℝ)*(major_s1_2) + (47114491/1000000000000 : ℝ)*(sp_s1_1) + (60409067/1000000000000 : ℝ)*(sp_s1_2) + (28272737/1000000000000 : ℝ)*(sp_s1_13) + (62930054061/40000000000 : ℝ)*(sp_s1_14) + (1206621325583/1000000000000 : ℝ)*(sp_s1_15) + (1206632024507/1000000000000 : ℝ)*(sp_s1_16) + (1973705726349/1000000000000 : ℝ)*(sp_s1_20) + (23993501/1000000000000 : ℝ)*(sp_s1_22) + (1045239953251/1000000000000 : ℝ)*(f.failure) + (62930054061/40000000000 : ℝ)*(f.sum) + (7273846521809591701/152682225150000000000000000000000 : ℝ)*base62 + (2967912095646539/4753050000000000000000000000 : ℝ)*base65 + (3530501503390861/4818450000000000000000000000 : ℝ)*base66 + (36273979922909/297065625000000000000000000 : ℝ)*base69 + (5657210579135559623/18272506593750000000000000000000 : ℝ)*base71 + (510308667371611/922650000000000000000000000 : ℝ)*base72 + (2109130553585513/2409225000000000000000000000 : ℝ)*base75 + (358578972219587/768875000000000000000000000 : ℝ)*base77 + (2172745505868336299/4939714325000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (1/762939453125 : ℝ)*base86 + (971/3125000000000000 : ℝ)*base88 + (971/3125000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(89257/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(89257/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2258403953374278811407400831967/313049455632550000000000000000000000 : ℝ) := by norm_num
    linear_combination (349531092823/500000000000 : ℝ)*(base7) + (23806486571/1000000000000 : ℝ)*(base33) + (3647551201/500000000000 : ℝ)*(base40) + (31454438441/31250000000 : ℝ)*(base43) + (44547/500000000000 : ℝ)*(base59) + (64772184783/40000000000 : ℝ)*(major_s1_0) + (318284538017/500000000000 : ℝ)*(major_s1_1) + (821555553073/500000000000 : ℝ)*(major_s1_2) + (1415003/1000000000000 : ℝ)*(sp_s1_1) + (13519/488281250 : ℝ)*(sp_s1_2) + (192435393317/250000000000 : ℝ)*(sp_s1_21) + (876237850903/500000000000 : ℝ)*(sp_s1_22) + (372953699893/500000000000 : ℝ)*(sp_s1_23) + (1773496629401/1000000000000 : ℝ)*(sp_s1_27) + (214886888751/200000000000 : ℝ)*(f.failure) + (88814180169/50000000000 : ℝ)*(f.sum) + (765335379485690453/10178815010000000000000000000000 : ℝ)*base62 + (1227679081916933/1188262500000000000000000000 : ℝ)*base64 + (1293062537433571/2409225000000000000000000000 : ℝ)*base67 + (2334236068278133/4753050000000000000000000000 : ℝ)*base69 + (3094415258184665933/7309002637500000000000000000000 : ℝ)*base70 + (937420706317/1230200000000000000000000 : ℝ)*base73 + (119206520709473/1204612500000000000000000000 : ℝ)*base74 + (26087526791209/61510000000000000000000000 : ℝ)*base76 + (1059288594267613517/1852392871875000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (221/625000000000000 : ℝ)*base86 + (221/625000000000000 : ℝ)*base88 + (221/625000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((18453/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18453/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-96369/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-96369/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(95061/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(95061/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((40551/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(40551/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-11353/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-11353/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(89257/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(89257/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c305086_s1 p hpa hpb X hX hprev0

#print axioms solution

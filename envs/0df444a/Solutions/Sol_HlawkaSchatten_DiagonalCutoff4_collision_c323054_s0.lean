-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c323054_s0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:52:24.694991+00:00
-- url     : https://prove2.me/submissions/253fb57c-babb-4039-9ae4-4f5633a6143d

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
theorem collision_support_c323054_s0_s0_0 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-913027/5000000000 : ℝ)*x 0 + (1155018043/2500000000 : ℝ)*x 1 + (-1681960223/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (913027/5000000000 : ℝ)^85 ≤ (2480951207/100000000000000 : ℝ)^69 := by
    have hnat : (913027 : ℕ)^85*100000000000000^69 ≤ 2480951207^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      913027 5000000000 2480951207 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1155018043/2500000000 : ℝ)^85 ≤ (38626570760143/100000000000000 : ℝ)^69 := by
    have hnat : (1155018043 : ℕ)^85*100000000000000^69 ≤ 38626570760143^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1155018043 2500000000 38626570760143 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1681960223/2500000000 : ℝ)^85 ≤ (15342737069357/25000000000000 : ℝ)^69 := by
    have hnat : (1681960223 : ℕ)^85*25000000000000^69 ≤ 15342737069357^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1681960223 2500000000 15342737069357 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-913027/5000000000 : ℝ), (1155018043/2500000000 : ℝ), (-1681960223/2500000000 : ℝ)] ![(2480951207/100000000000000 : ℝ), (38626570760143/100000000000000 : ℝ), (15342737069357/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-913027/5000000000 : ℝ)|^85 ≤ (2480951207/100000000000000 : ℝ)^69
        have hw : |(-913027/5000000000 : ℝ)|=(913027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1155018043/2500000000 : ℝ)|^85 ≤ (38626570760143/100000000000000 : ℝ)^69
        have hw : |(1155018043/2500000000 : ℝ)|=(1155018043/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1681960223/2500000000 : ℝ)|^85 ≤ (15342737069357/25000000000000 : ℝ)^69
        have hw : |(-1681960223/2500000000 : ℝ)|=(1681960223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323054_s0_s0_1 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5777900737/10000000000 : ℝ)*x 0 + (-1159654621/10000000000 : ℝ)*x 1 + (-2476595233/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5777900737/10000000000 : ℝ)^85 ≤ (50877803669453/100000000000000 : ℝ)^69 := by
    have hnat : (5777900737 : ℕ)^85*100000000000000^69 ≤ 50877803669453^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5777900737 10000000000 50877803669453 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1159654621/10000000000 : ℝ)^85 ≤ (3518288110353/50000000000000 : ℝ)^69 := by
    have hnat : (1159654621 : ℕ)^85*50000000000000^69 ≤ 3518288110353^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1159654621 10000000000 3518288110353 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2476595233/5000000000 : ℝ)^85 ≤ (4208562009707/10000000000000 : ℝ)^69 := by
    have hnat : (2476595233 : ℕ)^85*10000000000000^69 ≤ 4208562009707^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2476595233 5000000000 4208562009707 10000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5777900737/10000000000 : ℝ), (-1159654621/10000000000 : ℝ), (-2476595233/5000000000 : ℝ)] ![(50877803669453/100000000000000 : ℝ), (3518288110353/50000000000000 : ℝ), (4208562009707/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5777900737/10000000000 : ℝ)|^85 ≤ (50877803669453/100000000000000 : ℝ)^69
        have hw : |(5777900737/10000000000 : ℝ)|=(5777900737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1159654621/10000000000 : ℝ)|^85 ≤ (3518288110353/50000000000000 : ℝ)^69
        have hw : |(-1159654621/10000000000 : ℝ)|=(1159654621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2476595233/5000000000 : ℝ)|^85 ≤ (4208562009707/10000000000000 : ℝ)^69
        have hw : |(-2476595233/5000000000 : ℝ)|=(2476595233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323054_s0_s0_2 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5367706637/10000000000 : ℝ)*x 0 + (1341926659/2500000000 : ℝ)*x 1 + (1163976691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5367706637/10000000000 : ℝ)^85 ≤ (46465551499389/100000000000000 : ℝ)^69 := by
    have hnat : (5367706637 : ℕ)^85*100000000000000^69 ≤ 46465551499389^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367706637 10000000000 46465551499389 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1341926659/2500000000 : ℝ)^85 ≤ (1858622059549/4000000000000 : ℝ)^69 := by
    have hnat : (1341926659 : ℕ)^85*4000000000000^69 ≤ 1858622059549^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1341926659 2500000000 1858622059549 4000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1163976691/10000000000 : ℝ)^85 ≤ (883612124899/12500000000000 : ℝ)^69 := by
    have hnat : (1163976691 : ℕ)^85*12500000000000^69 ≤ 883612124899^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1163976691 10000000000 883612124899 12500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5367706637/10000000000 : ℝ), (1341926659/2500000000 : ℝ), (1163976691/10000000000 : ℝ)] ![(46465551499389/100000000000000 : ℝ), (1858622059549/4000000000000 : ℝ), (883612124899/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5367706637/10000000000 : ℝ)|^85 ≤ (46465551499389/100000000000000 : ℝ)^69
        have hw : |(5367706637/10000000000 : ℝ)|=(5367706637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1341926659/2500000000 : ℝ)|^85 ≤ (1858622059549/4000000000000 : ℝ)^69
        have hw : |(1341926659/2500000000 : ℝ)|=(1341926659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1163976691/10000000000 : ℝ)|^85 ≤ (883612124899/12500000000000 : ℝ)^69
        have hw : |(1163976691/10000000000 : ℝ)|=(1163976691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323054_s0_s0_7 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-8700873/312500000 : ℝ)*x 0 + (1024725001/10000000000 : ℝ)*x 1 + (-4703436543/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8700873/312500000 : ℝ)^85 ≤ (4854298673/400000000000 : ℝ)^69 := by
    have hnat : (8700873 : ℕ)^85*400000000000^69 ≤ 4854298673^69*312500000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8700873 312500000 4854298673 400000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1024725001/10000000000 : ℝ)^85 ≤ (6042030947333/100000000000000 : ℝ)^69 := by
    have hnat : (1024725001 : ℕ)^85*100000000000000^69 ≤ 6042030947333^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024725001 10000000000 6042030947333 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4703436543/5000000000 : ℝ)^85 ≤ (23186098593153/25000000000000 : ℝ)^69 := by
    have hnat : (4703436543 : ℕ)^85*25000000000000^69 ≤ 23186098593153^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4703436543 5000000000 23186098593153 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-8700873/312500000 : ℝ), (1024725001/10000000000 : ℝ), (-4703436543/5000000000 : ℝ)] ![(4854298673/400000000000 : ℝ), (6042030947333/100000000000000 : ℝ), (23186098593153/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-8700873/312500000 : ℝ)|^85 ≤ (4854298673/400000000000 : ℝ)^69
        have hw : |(-8700873/312500000 : ℝ)|=(8700873/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1024725001/10000000000 : ℝ)|^85 ≤ (6042030947333/100000000000000 : ℝ)^69
        have hw : |(1024725001/10000000000 : ℝ)|=(1024725001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4703436543/5000000000 : ℝ)|^85 ≤ (23186098593153/25000000000000 : ℝ)^69
        have hw : |(-4703436543/5000000000 : ℝ)|=(4703436543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323054_s0_s0_8 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (129636207/400000000 : ℝ)*x 0 + (-427170627/10000000000 : ℝ)*x 1 + (-3872177351/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129636207/400000000 : ℝ)^85 ≤ (24957302663911/100000000000000 : ℝ)^69 := by
    have hnat : (129636207 : ℕ)^85*100000000000000^69 ≤ 24957302663911^69*400000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129636207 400000000 24957302663911 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (427170627/10000000000 : ℝ)^85 ≤ (2056173102623/100000000000000 : ℝ)^69 := by
    have hnat : (427170627 : ℕ)^85*100000000000000^69 ≤ 2056173102623^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427170627 10000000000 2056173102623 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3872177351/5000000000 : ℝ)^85 ≤ (72986524219113/100000000000000 : ℝ)^69 := by
    have hnat : (3872177351 : ℕ)^85*100000000000000^69 ≤ 72986524219113^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3872177351 5000000000 72986524219113 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(129636207/400000000 : ℝ), (-427170627/10000000000 : ℝ), (-3872177351/5000000000 : ℝ)] ![(24957302663911/100000000000000 : ℝ), (2056173102623/100000000000000 : ℝ), (72986524219113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(129636207/400000000 : ℝ)|^85 ≤ (24957302663911/100000000000000 : ℝ)^69
        have hw : |(129636207/400000000 : ℝ)|=(129636207/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-427170627/10000000000 : ℝ)|^85 ≤ (2056173102623/100000000000000 : ℝ)^69
        have hw : |(-427170627/10000000000 : ℝ)|=(427170627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3872177351/5000000000 : ℝ)|^85 ≤ (72986524219113/100000000000000 : ℝ)^69
        have hw : |(-3872177351/5000000000 : ℝ)|=(3872177351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323054_s0_s0_9 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1407540039/5000000000 : ℝ)*x 0 + (8113352663/10000000000 : ℝ)*x 1 + (46292609/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1407540039/5000000000 : ℝ)^85 ≤ (20981495261569/100000000000000 : ℝ)^69 := by
    have hnat : (1407540039 : ℕ)^85*100000000000000^69 ≤ 20981495261569^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1407540039 5000000000 20981495261569 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8113352663/10000000000 : ℝ)^85 ≤ (38646962681439/50000000000000 : ℝ)^69 := by
    have hnat : (8113352663 : ℕ)^85*50000000000000^69 ≤ 38646962681439^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8113352663 10000000000 38646962681439 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (46292609/1250000000 : ℝ)^85 ≤ (86228968307/5000000000000 : ℝ)^69 := by
    have hnat : (46292609 : ℕ)^85*5000000000000^69 ≤ 86228968307^69*1250000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46292609 1250000000 86228968307 5000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1407540039/5000000000 : ℝ), (8113352663/10000000000 : ℝ), (46292609/1250000000 : ℝ)] ![(20981495261569/100000000000000 : ℝ), (38646962681439/50000000000000 : ℝ), (86228968307/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1407540039/5000000000 : ℝ)|^85 ≤ (20981495261569/100000000000000 : ℝ)^69
        have hw : |(1407540039/5000000000 : ℝ)|=(1407540039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8113352663/10000000000 : ℝ)|^85 ≤ (38646962681439/50000000000000 : ℝ)^69
        have hw : |(8113352663/10000000000 : ℝ)|=(8113352663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(46292609/1250000000 : ℝ)|^85 ≤ (86228968307/5000000000000 : ℝ)^69
        have hw : |(46292609/1250000000 : ℝ)|=(46292609/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323054_s0_s0_13 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (30950371/100000000 : ℝ)*x 0 + (3950212479/5000000000 : ℝ)*x 1 + (-351379741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (30950371/100000000 : ℝ)^85 ≤ (23580846531421/100000000000000 : ℝ)^69 := by
    have hnat : (30950371 : ℕ)^85*100000000000000^69 ≤ 23580846531421^69*100000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30950371 100000000 23580846531421 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3950212479/5000000000 : ℝ)^85 ≤ (74802691363449/100000000000000 : ℝ)^69 := by
    have hnat : (3950212479 : ℕ)^85*100000000000000^69 ≤ 74802691363449^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3950212479 5000000000 74802691363449 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (351379741/10000000000 : ℝ)^85 ≤ (1616462085723/100000000000000 : ℝ)^69 := by
    have hnat : (351379741 : ℕ)^85*100000000000000^69 ≤ 1616462085723^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      351379741 10000000000 1616462085723 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(30950371/100000000 : ℝ), (3950212479/5000000000 : ℝ), (-351379741/10000000000 : ℝ)] ![(23580846531421/100000000000000 : ℝ), (74802691363449/100000000000000 : ℝ), (1616462085723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(30950371/100000000 : ℝ)|^85 ≤ (23580846531421/100000000000000 : ℝ)^69
        have hw : |(30950371/100000000 : ℝ)|=(30950371/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3950212479/5000000000 : ℝ)|^85 ≤ (74802691363449/100000000000000 : ℝ)^69
        have hw : |(3950212479/5000000000 : ℝ)|=(3950212479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-351379741/10000000000 : ℝ)|^85 ≤ (1616462085723/100000000000000 : ℝ)^69
        have hw : |(-351379741/10000000000 : ℝ)|=(351379741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323054_s0_s0_14 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-121/2000000000 : ℝ)*x 0 + (428481949/2500000000 : ℝ)*x 1 + (-9065351039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (121/2000000000 : ℝ)^85 ≤ (64111/50000000000000 : ℝ)^69 := by
    have hnat : (121 : ℕ)^85*50000000000000^69 ≤ 64111^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121 2000000000 64111 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (428481949/2500000000 : ℝ)^85 ≤ (11385906148379/100000000000000 : ℝ)^69 := by
    have hnat : (428481949 : ℕ)^85*100000000000000^69 ≤ 11385906148379^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428481949 2500000000 11385906148379 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9065351039/10000000000 : ℝ)^85 ≤ (5538380857023/6250000000000 : ℝ)^69 := by
    have hnat : (9065351039 : ℕ)^85*6250000000000^69 ≤ 5538380857023^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9065351039 10000000000 5538380857023 6250000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-121/2000000000 : ℝ), (428481949/2500000000 : ℝ), (-9065351039/10000000000 : ℝ)] ![(64111/50000000000000 : ℝ), (11385906148379/100000000000000 : ℝ), (5538380857023/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-121/2000000000 : ℝ)|^85 ≤ (64111/50000000000000 : ℝ)^69
        have hw : |(-121/2000000000 : ℝ)|=(121/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(428481949/2500000000 : ℝ)|^85 ≤ (11385906148379/100000000000000 : ℝ)^69
        have hw : |(428481949/2500000000 : ℝ)|=(428481949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-9065351039/10000000000 : ℝ)|^85 ≤ (5538380857023/6250000000000 : ℝ)^69
        have hw : |(-9065351039/10000000000 : ℝ)|=(9065351039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323054_s0_s0_15 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (535779331/2500000000 : ℝ)*x 0 + (-3718385651/10000000000 : ℝ)*x 1 + (-6195429849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535779331/2500000000 : ℝ)^85 ≤ (14994298989917/100000000000000 : ℝ)^69 := by
    have hnat : (535779331 : ℕ)^85*100000000000000^69 ≤ 14994298989917^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535779331 2500000000 14994298989917 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3718385651/10000000000 : ℝ)^85 ≤ (29561500353959/100000000000000 : ℝ)^69 := by
    have hnat : (3718385651 : ℕ)^85*100000000000000^69 ≤ 29561500353959^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3718385651 10000000000 29561500353959 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6195429849/10000000000 : ℝ)^85 ≤ (55444200636293/100000000000000 : ℝ)^69 := by
    have hnat : (6195429849 : ℕ)^85*100000000000000^69 ≤ 55444200636293^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6195429849 10000000000 55444200636293 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535779331/2500000000 : ℝ), (-3718385651/10000000000 : ℝ), (-6195429849/10000000000 : ℝ)] ![(14994298989917/100000000000000 : ℝ), (29561500353959/100000000000000 : ℝ), (55444200636293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535779331/2500000000 : ℝ)|^85 ≤ (14994298989917/100000000000000 : ℝ)^69
        have hw : |(535779331/2500000000 : ℝ)|=(535779331/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3718385651/10000000000 : ℝ)|^85 ≤ (29561500353959/100000000000000 : ℝ)^69
        have hw : |(-3718385651/10000000000 : ℝ)|=(3718385651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6195429849/10000000000 : ℝ)|^85 ≤ (55444200636293/100000000000000 : ℝ)^69
        have hw : |(-6195429849/10000000000 : ℝ)|=(6195429849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323054_s0_s0_16 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8188540231/10000000000 : ℝ)*x 0 + (93677227/400000000 : ℝ)*x 1 + (892556309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8188540231/10000000000 : ℝ)^85 ≤ (39088630913147/50000000000000 : ℝ)^69 := by
    have hnat : (8188540231 : ℕ)^85*50000000000000^69 ≤ 39088630913147^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8188540231 10000000000 39088630913147 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (93677227/400000000 : ℝ)^85 ≤ (16725854099943/100000000000000 : ℝ)^69 := by
    have hnat : (93677227 : ℕ)^85*100000000000000^69 ≤ 16725854099943^69*400000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93677227 400000000 16725854099943 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (892556309/10000000000 : ℝ)^85 ≤ (2548442028003/50000000000000 : ℝ)^69 := by
    have hnat : (892556309 : ℕ)^85*50000000000000^69 ≤ 2548442028003^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      892556309 10000000000 2548442028003 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8188540231/10000000000 : ℝ), (93677227/400000000 : ℝ), (892556309/10000000000 : ℝ)] ![(39088630913147/50000000000000 : ℝ), (16725854099943/100000000000000 : ℝ), (2548442028003/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8188540231/10000000000 : ℝ)|^85 ≤ (39088630913147/50000000000000 : ℝ)^69
        have hw : |(8188540231/10000000000 : ℝ)|=(8188540231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(93677227/400000000 : ℝ)|^85 ≤ (16725854099943/100000000000000 : ℝ)^69
        have hw : |(93677227/400000000 : ℝ)|=(93677227/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(892556309/10000000000 : ℝ)|^85 ≤ (2548442028003/50000000000000 : ℝ)^69
        have hw : |(892556309/10000000000 : ℝ)|=(892556309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323054_s0_s0_20 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1935570743/2500000000 : ℝ)*x 0 + (1517457191/5000000000 : ℝ)*x 1 + (-736093643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1935570743/2500000000 : ℝ)^85 ≤ (14592494490681/20000000000000 : ℝ)^69 := by
    have hnat : (1935570743 : ℕ)^85*20000000000000^69 ≤ 14592494490681^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1935570743 2500000000 14592494490681 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1517457191/5000000000 : ℝ)^85 ≤ (2301783431451/10000000000000 : ℝ)^69 := by
    have hnat : (1517457191 : ℕ)^85*10000000000000^69 ≤ 2301783431451^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1517457191 5000000000 2301783431451 10000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (736093643/10000000000 : ℝ)^85 ≤ (2009846607499/50000000000000 : ℝ)^69 := by
    have hnat : (736093643 : ℕ)^85*50000000000000^69 ≤ 2009846607499^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      736093643 10000000000 2009846607499 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1935570743/2500000000 : ℝ), (1517457191/5000000000 : ℝ), (-736093643/10000000000 : ℝ)] ![(14592494490681/20000000000000 : ℝ), (2301783431451/10000000000000 : ℝ), (2009846607499/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1935570743/2500000000 : ℝ)|^85 ≤ (14592494490681/20000000000000 : ℝ)^69
        have hw : |(1935570743/2500000000 : ℝ)|=(1935570743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1517457191/5000000000 : ℝ)|^85 ≤ (2301783431451/10000000000000 : ℝ)^69
        have hw : |(1517457191/5000000000 : ℝ)|=(1517457191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-736093643/10000000000 : ℝ)|^85 ≤ (2009846607499/50000000000000 : ℝ)^69
        have hw : |(-736093643/10000000000 : ℝ)|=(736093643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323054_s0_s0_21 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (50407/1000000000 : ℝ)*x 0 + (1336870143/2000000000 : ℝ)*x 1 + (-233381101/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (50407/1000000000 : ℝ)^85 ≤ (508120821/100000000000000 : ℝ)^69 := by
    have hnat : (50407 : ℕ)^85*100000000000000^69 ≤ 508120821^69*1000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50407 1000000000 508120821 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1336870143/2000000000 : ℝ)^85 ≤ (30441304319743/50000000000000 : ℝ)^69 := by
    have hnat : (1336870143 : ℕ)^85*50000000000000^69 ≤ 30441304319743^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336870143 2000000000 30441304319743 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (233381101/500000000 : ℝ)^85 ≤ (19558441609261/50000000000000 : ℝ)^69 := by
    have hnat : (233381101 : ℕ)^85*50000000000000^69 ≤ 19558441609261^69*500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233381101 500000000 19558441609261 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(50407/1000000000 : ℝ), (1336870143/2000000000 : ℝ), (-233381101/500000000 : ℝ)] ![(508120821/100000000000000 : ℝ), (30441304319743/50000000000000 : ℝ), (19558441609261/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(50407/1000000000 : ℝ)|^85 ≤ (508120821/100000000000000 : ℝ)^69
        have hw : |(50407/1000000000 : ℝ)|=(50407/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1336870143/2000000000 : ℝ)|^85 ≤ (30441304319743/50000000000000 : ℝ)^69
        have hw : |(1336870143/2000000000 : ℝ)|=(1336870143/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-233381101/500000000 : ℝ)|^85 ≤ (19558441609261/50000000000000 : ℝ)^69
        have hw : |(-233381101/500000000 : ℝ)|=(233381101/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323054_s0_s0_22 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8300685047/10000000000 : ℝ)*x 0 + (-1615830221/10000000000 : ℝ)*x 1 + (-1531657651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8300685047/10000000000 : ℝ)^85 ≤ (993728532991/1250000000000 : ℝ)^69 := by
    have hnat : (8300685047 : ℕ)^85*1250000000000^69 ≤ 993728532991^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8300685047 10000000000 993728532991 1250000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1615830221/10000000000 : ℝ)^85 ≤ (10588521316769/100000000000000 : ℝ)^69 := by
    have hnat : (1615830221 : ℕ)^85*100000000000000^69 ≤ 10588521316769^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1615830221 10000000000 10588521316769 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1531657651/10000000000 : ℝ)^85 ≤ (2478299006701/25000000000000 : ℝ)^69 := by
    have hnat : (1531657651 : ℕ)^85*25000000000000^69 ≤ 2478299006701^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1531657651 10000000000 2478299006701 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8300685047/10000000000 : ℝ), (-1615830221/10000000000 : ℝ), (-1531657651/10000000000 : ℝ)] ![(993728532991/1250000000000 : ℝ), (10588521316769/100000000000000 : ℝ), (2478299006701/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8300685047/10000000000 : ℝ)|^85 ≤ (993728532991/1250000000000 : ℝ)^69
        have hw : |(8300685047/10000000000 : ℝ)|=(8300685047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1615830221/10000000000 : ℝ)|^85 ≤ (10588521316769/100000000000000 : ℝ)^69
        have hw : |(-1615830221/10000000000 : ℝ)|=(1615830221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1531657651/10000000000 : ℝ)|^85 ≤ (2478299006701/25000000000000 : ℝ)^69
        have hw : |(-1531657651/10000000000 : ℝ)|=(1531657651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323054_s0_s0_23 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1572962081/10000000000 : ℝ)*x 0 + (3584471887/5000000000 : ℝ)*x 1 + (1537434541/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1572962081/10000000000 : ℝ)^85 ≤ (1024353892809/10000000000000 : ℝ)^69 := by
    have hnat : (1572962081 : ℕ)^85*10000000000000^69 ≤ 1024353892809^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1572962081 10000000000 1024353892809 10000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3584471887/5000000000 : ℝ)^85 ≤ (66364760811571/100000000000000 : ℝ)^69 := by
    have hnat : (3584471887 : ℕ)^85*100000000000000^69 ≤ 66364760811571^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3584471887 5000000000 66364760811571 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1537434541/5000000000 : ℝ)^85 ≤ (58479250631/250000000000 : ℝ)^69 := by
    have hnat : (1537434541 : ℕ)^85*250000000000^69 ≤ 58479250631^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1537434541 5000000000 58479250631 250000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1572962081/10000000000 : ℝ), (3584471887/5000000000 : ℝ), (1537434541/5000000000 : ℝ)] ![(1024353892809/10000000000000 : ℝ), (66364760811571/100000000000000 : ℝ), (58479250631/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1572962081/10000000000 : ℝ)|^85 ≤ (1024353892809/10000000000000 : ℝ)^69
        have hw : |(1572962081/10000000000 : ℝ)|=(1572962081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3584471887/5000000000 : ℝ)|^85 ≤ (66364760811571/100000000000000 : ℝ)^69
        have hw : |(3584471887/5000000000 : ℝ)|=(3584471887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1537434541/5000000000 : ℝ)|^85 ≤ (58479250631/250000000000 : ℝ)^69
        have hw : |(1537434541/5000000000 : ℝ)|=(1537434541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323054_s0_s0_27 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7364661263/10000000000 : ℝ)*x 0 + (378095863/1250000000 : ℝ)*x 1 + (-1348427969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7364661263/10000000000 : ℝ)^85 ≤ (68603713246199/100000000000000 : ℝ)^69 := by
    have hnat : (7364661263 : ℕ)^85*100000000000000^69 ≤ 68603713246199^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7364661263 10000000000 68603713246199 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (378095863/1250000000 : ℝ)^85 ≤ (2865382860581/12500000000000 : ℝ)^69 := by
    have hnat : (378095863 : ℕ)^85*12500000000000^69 ≤ 2865382860581^69*1250000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      378095863 1250000000 2865382860581 12500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348427969/10000000000 : ℝ)^85 ≤ (1059152981459/12500000000000 : ℝ)^69 := by
    have hnat : (1348427969 : ℕ)^85*12500000000000^69 ≤ 1059152981459^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348427969 10000000000 1059152981459 12500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7364661263/10000000000 : ℝ), (378095863/1250000000 : ℝ), (-1348427969/10000000000 : ℝ)] ![(68603713246199/100000000000000 : ℝ), (2865382860581/12500000000000 : ℝ), (1059152981459/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7364661263/10000000000 : ℝ)|^85 ≤ (68603713246199/100000000000000 : ℝ)^69
        have hw : |(7364661263/10000000000 : ℝ)|=(7364661263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(378095863/1250000000 : ℝ)|^85 ≤ (2865382860581/12500000000000 : ℝ)^69
        have hw : |(378095863/1250000000 : ℝ)|=(378095863/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1348427969/10000000000 : ℝ)|^85 ≤ (1059152981459/12500000000000 : ℝ)^69
        have hw : |(-1348427969/10000000000 : ℝ)|=(1348427969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c323054_s0 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (97817/50000 : ℝ) (166881/100000 : ℝ) (80913/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]]) : (0 : ℝ) ≤ ((4171/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4171/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(70347/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(70347/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-31053/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-31053/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (80913/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (80913/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (80913/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (80913/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (80913/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (80913/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (166881/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
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
  have s0_pow0 : (1 : ℝ) ^ (83/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^83 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^83*1^16 ≤ 1^16*1^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2285913930952523/2000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2285913930952523/2000000000000000 : ℝ)^83 := by
      have hnat : (2 : ℕ)^16*2000000000000000^83 ≤ 2285913930952523^83*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2285913930952523 2000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2285913930952523/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (1544846006891271/1250000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (1544846006891271/1250000000000000 : ℝ)^83 := by
      have hnat : (3 : ℕ)^16*1250000000000000^83 ≤ 1544846006891271^83*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 1544846006891271 1250000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1544846006891271/1250000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(285913930952523/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(929198400367553/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (285913930952523/2000000000000000 : ℝ)) (beta := (929198400367553/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(285913930952523/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(929198400367553/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (83/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^83 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^83*1^16 ≤ 1^16*1^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2285913930952523/2000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2285913930952523/2000000000000000 : ℝ)^83 := by
      have hnat : (2 : ℕ)^16*2000000000000000^83 ≤ 2285913930952523^83*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2285913930952523 2000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2285913930952523/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (1544846006891271/1250000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (1544846006891271/1250000000000000 : ℝ)^83 := by
      have hnat : (3 : ℕ)^16*1250000000000000^83 ≤ 1544846006891271^83*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 1544846006891271 1250000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1544846006891271/1250000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(285913930952523/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(929198400367553/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (285913930952523/2000000000000000 : ℝ)) (beta := (929198400367553/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(285913930952523/2000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(929198400367553/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (83/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^83 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^83*1^16 ≤ 1^16*1^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2285913930952523/2000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2285913930952523/2000000000000000 : ℝ)^83 := by
      have hnat : (2 : ℕ)^16*2000000000000000^83 ≤ 2285913930952523^83*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2285913930952523 2000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2285913930952523/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (1544846006891271/1250000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (1544846006891271/1250000000000000 : ℝ)^83 := by
      have hnat : (3 : ℕ)^16*1250000000000000^83 ≤ 1544846006891271^83*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 1544846006891271 1250000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1544846006891271/1250000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(285913930952523/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(929198400367553/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (285913930952523/2000000000000000 : ℝ)) (beta := (929198400367553/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(285913930952523/2000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(929198400367553/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-913027/5000000000 : ℝ)*X 0 0+(1155018043/2500000000 : ℝ)*X 0 1+(-1681960223/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323054_s0_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((5777900737/10000000000 : ℝ)*X 1 0+(-1159654621/10000000000 : ℝ)*X 1 1+(-2476595233/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323054_s0_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((5367706637/10000000000 : ℝ)*X 2 0+(1341926659/2500000000 : ℝ)*X 2 1+(1163976691/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323054_s0_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-8700873/312500000 : ℝ)*X 0 0+(1024725001/10000000000 : ℝ)*X 0 1+(-4703436543/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323054_s0_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((129636207/400000000 : ℝ)*X 1 0+(-427170627/10000000000 : ℝ)*X 1 1+(-3872177351/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323054_s0_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1407540039/5000000000 : ℝ)*X 2 0+(8113352663/10000000000 : ℝ)*X 2 1+(46292609/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323054_s0_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((30950371/100000000 : ℝ)*X 0 0+(3950212479/5000000000 : ℝ)*X 0 1+(-351379741/10000000000 : ℝ)*X 0 2+(30950371/100000000 : ℝ)*X 1 0+(3950212479/5000000000 : ℝ)*X 1 1+(-351379741/10000000000 : ℝ)*X 1 2+(30950371/100000000 : ℝ)*X 2 0+(3950212479/5000000000 : ℝ)*X 2 1+(-351379741/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323054_s0_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-121/2000000000 : ℝ)*X 0 0+(428481949/2500000000 : ℝ)*X 0 1+(-9065351039/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323054_s0_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((535779331/2500000000 : ℝ)*X 1 0+(-3718385651/10000000000 : ℝ)*X 1 1+(-6195429849/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323054_s0_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((8188540231/10000000000 : ℝ)*X 2 0+(93677227/400000000 : ℝ)*X 2 1+(892556309/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323054_s0_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((1935570743/2500000000 : ℝ)*X 0 0+(1517457191/5000000000 : ℝ)*X 0 1+(-736093643/10000000000 : ℝ)*X 0 2+(1935570743/2500000000 : ℝ)*X 1 0+(1517457191/5000000000 : ℝ)*X 1 1+(-736093643/10000000000 : ℝ)*X 1 2+(1935570743/2500000000 : ℝ)*X 2 0+(1517457191/5000000000 : ℝ)*X 2 1+(-736093643/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323054_s0_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((50407/1000000000 : ℝ)*X 0 0+(1336870143/2000000000 : ℝ)*X 0 1+(-233381101/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323054_s0_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((8300685047/10000000000 : ℝ)*X 1 0+(-1615830221/10000000000 : ℝ)*X 1 1+(-1531657651/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323054_s0_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((1572962081/10000000000 : ℝ)*X 2 0+(3584471887/5000000000 : ℝ)*X 2 1+(1537434541/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323054_s0_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((7364661263/10000000000 : ℝ)*X 0 0+(378095863/1250000000 : ℝ)*X 0 1+(-1348427969/10000000000 : ℝ)*X 0 2+(7364661263/10000000000 : ℝ)*X 1 0+(378095863/1250000000 : ℝ)*X 1 1+(-1348427969/10000000000 : ℝ)*X 1 2+(7364661263/10000000000 : ℝ)*X 2 0+(378095863/1250000000 : ℝ)*X 2 1+(-1348427969/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323054_s0_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((4171/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4171/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3997756375765241041023/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (480010703581/500000000000 : ℝ)*(base7) + (155851/200000000000 : ℝ)*(base39) + (5594633/500000000000 : ℝ)*(base53) + (6851434389/100000000000 : ℝ)*(base60) + (71968825663/50000000000 : ℝ)*(major_s0_0) + (71968825663/50000000000 : ℝ)*(major_s0_1) + (719682661997/500000000000 : ℝ)*(major_s0_2) + (2463531/250000000000 : ℝ)*(sp_s0_1) + (804461283763/500000000000 : ℝ)*(sp_s0_7) + (1608948024737/1000000000000 : ℝ)*(sp_s0_8) + (804485057123/500000000000 : ℝ)*(sp_s0_9) + (1695771079131/1000000000000 : ℝ)*(sp_s0_13) + (18178727/500000000000 : ℝ)*(sp_s0_14) + (26153/25000000000 : ℝ)*(sp_s0_15) + (735749671969/1000000000000 : ℝ)*(f.failure) + (804485057123/500000000000 : ℝ)*(f.sum) + (150289776054079/1000000000000000000000000000 : ℝ)*base62 + (5299396060983341/5000000000000000000000000000 : ℝ)*base65 + (286767728262639/500000000000000000000000000 : ℝ)*base66 + (248708170931569/1000000000000000000000000000 : ℝ)*base68 + (4232181977370791/5000000000000000000000000000 : ℝ)*base71 + (6064715637361/500000000000000000000000000 : ℝ)*base72 + (57353804117749/100000000000000000000000000 : ℝ)*base75 + (81710431037749/100000000000000000000000000 : ℝ)*base77 + (1461977441/10000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (8327/50000000000000000 : ℝ)*base86 + (8327/50000000000000000 : ℝ)*base88 + (8327/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(70347/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(70347/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10003680143344333017741/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1075994366391/1000000000000 : ℝ)*(base7) + (143186220697/250000000000 : ℝ)*(base53) + (13573246139/200000000000 : ℝ)*(base60) + (278448662649/200000000000 : ℝ)*(major_s0_0) + (278448662649/200000000000 : ℝ)*(major_s0_1) + (819498430457/1000000000000 : ℝ)*(major_s0_2) + (171561/125000000000 : ℝ)*(sp_s0_0) + (1626919/500000000000 : ℝ)*(sp_s0_1) + (2825823/500000000000 : ℝ)*(sp_s0_8) + (112692314923/125000000000 : ℝ)*(sp_s0_14) + (901530986387/1000000000000 : ℝ)*(sp_s0_15) + (73714238733/50000000000 : ℝ)*(sp_s0_16) + (89382307641/50000000000 : ℝ)*(sp_s0_20) + (5345381/1000000000000 : ℝ)*(sp_s0_27) + (71165713181/100000000000 : ℝ)*(f.failure) + (73714238733/50000000000 : ℝ)*(f.sum) + (480877858969927/1000000000000000000000000000 : ℝ)*base62 + (1901246145761721/10000000000000000000000000000 : ℝ)*base65 + (586817841572103/2000000000000000000000000000 : ℝ)*base67 + (719784973206989/2000000000000000000000000000 : ℝ)*base68 + (596992420774349/2500000000000000000000000000 : ℝ)*base71 + (760797494972103/2000000000000000000000000000 : ℝ)*base72 + (117916085706573/400000000000000000000000000 : ℝ)*base74 + (97148864146573/400000000000000000000000000 : ℝ)*base76 + (27554509/10000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (877/5000000000000000 : ℝ)*base87 + (877/5000000000000000 : ℝ)*base89 + (877/5000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-31053/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-31053/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (80276664265516218187113/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (295190382103/250000000000 : ℝ)*(base7) + (12855789/1000000000000 : ℝ)*(base15) + (99302389389/500000000000 : ℝ)*(base39) + (8995219/1000000000000 : ℝ)*(base43) + (719759437741/500000000000 : ℝ)*(major_s0_0) + (1439509880263/1000000000000 : ℝ)*(major_s0_1) + (719759437741/500000000000 : ℝ)*(major_s0_2) + (174033/50000000000 : ℝ)*(sp_s0_2) + (11976957/1000000000000 : ℝ)*(sp_s0_9) + (82579789/1000000000000 : ℝ)*(sp_s0_20) + (743189373457/500000000000 : ℝ)*(sp_s0_21) + (185796860793/125000000000 : ℝ)*(sp_s0_22) + (1486363289297/1000000000000 : ℝ)*(sp_s0_23) + (383300278053/200000000000 : ℝ)*(sp_s0_27) + (367911220821/500000000000 : ℝ)*(f.failure) + (1486387742133/1000000000000 : ℝ)*(f.sum) + (102675168378927/400000000000000000000000000 : ℝ)*base63 + (742624213982227/5000000000000000000000000000 : ℝ)*base64 + (559595171693561/10000000000000000000000000000 : ℝ)*base67 + (60835468270543/1000000000000000000000000000 : ℝ)*base69 + (66287972483811/625000000000000000000000000 : ℝ)*base71 + (875184451982227/5000000000000000000000000000 : ℝ)*base72 + (202051722553549/2000000000000000000000000000 : ℝ)*base75 + (142713763329457/1000000000000000000000000000 : ℝ)*base76 + (1436138986270893/10000000000000000000000000000 : ℝ)*base78 + (2243/25000000000000000 : ℝ)*base86 + (2243/25000000000000000 : ℝ)*base88 + (2243/25000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (97817/50000 : ℝ) (166881/100000 : ℝ) (80913/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]]) : (0 : ℝ) ≤ ((4171/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4171/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(70347/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(70347/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-31053/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-31053/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c323054_s0 p hpa hpb X hX

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c308054_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:36:58.163061+00:00
-- url     : https://prove2.me/submissions/79dd24a5-14ff-4ba6-9297-dd7d6c00d9a3

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
theorem collision_support_c308054_s1_s1_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5921116991/10000000000 : ℝ)*x 0 + (-367937637/2500000000 : ℝ)*x 1 + (-5060531129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5921116991/10000000000 : ℝ)^69 ≤ (50546990990889/100000000000000 : ℝ)^53 := by
    have hnat : (5921116991 : ℕ)^69*100000000000000^53 ≤ 50546990990889^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5921116991 10000000000 50546990990889 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (367937637/2500000000 : ℝ)^69 ≤ (8253047485437/100000000000000 : ℝ)^53 := by
    have hnat : (367937637 : ℕ)^69*100000000000000^53 ≤ 8253047485437^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      367937637 2500000000 8253047485437 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5060531129/10000000000 : ℝ)^69 ≤ (10299990378189/25000000000000 : ℝ)^53 := by
    have hnat : (5060531129 : ℕ)^69*25000000000000^53 ≤ 10299990378189^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5060531129 10000000000 10299990378189 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5921116991/10000000000 : ℝ), (-367937637/2500000000 : ℝ), (-5060531129/10000000000 : ℝ)] ![(50546990990889/100000000000000 : ℝ), (8253047485437/100000000000000 : ℝ), (10299990378189/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5921116991/10000000000 : ℝ)|^69 ≤ (50546990990889/100000000000000 : ℝ)^53
        have hw : |(5921116991/10000000000 : ℝ)|=(5921116991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-367937637/2500000000 : ℝ)|^69 ≤ (8253047485437/100000000000000 : ℝ)^53
        have hw : |(-367937637/2500000000 : ℝ)|=(367937637/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5060531129/10000000000 : ℝ)|^69 ≤ (10299990378189/25000000000000 : ℝ)^53
        have hw : |(-5060531129/10000000000 : ℝ)|=(5060531129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308054_s1_s1_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (279871809/500000000 : ℝ)*x 0 + (55528563/100000000 : ℝ)*x 1 + (1229044127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (279871809/500000000 : ℝ)^69 ≤ (46979717790347/100000000000000 : ℝ)^53 := by
    have hnat : (279871809 : ℕ)^69*100000000000000^53 ≤ 46979717790347^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279871809 500000000 46979717790347 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (55528563/100000000 : ℝ)^69 ≤ (4649318738119/10000000000000 : ℝ)^53 := by
    have hnat : (55528563 : ℕ)^69*10000000000000^53 ≤ 4649318738119^53*100000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55528563 100000000 4649318738119 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1229044127/10000000000 : ℝ)^69 ≤ (815886851767/12500000000000 : ℝ)^53 := by
    have hnat : (1229044127 : ℕ)^69*12500000000000^53 ≤ 815886851767^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1229044127 10000000000 815886851767 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(279871809/500000000 : ℝ), (55528563/100000000 : ℝ), (1229044127/10000000000 : ℝ)] ![(46979717790347/100000000000000 : ℝ), (4649318738119/10000000000000 : ℝ), (815886851767/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(279871809/500000000 : ℝ)|^69 ≤ (46979717790347/100000000000000 : ℝ)^53
        have hw : |(279871809/500000000 : ℝ)|=(279871809/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(55528563/100000000 : ℝ)|^69 ≤ (4649318738119/10000000000000 : ℝ)^53
        have hw : |(55528563/100000000 : ℝ)|=(55528563/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1229044127/10000000000 : ℝ)|^69 ≤ (815886851767/12500000000000 : ℝ)^53
        have hw : |(1229044127/10000000000 : ℝ)|=(1229044127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308054_s1_s1_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5479733297/10000000000 : ℝ)*x 0 + (136221611/250000000 : ℝ)*x 1 + (-1564895559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5479733297/10000000000 : ℝ)^69 ≤ (45697699894859/100000000000000 : ℝ)^53 := by
    have hnat : (5479733297 : ℕ)^69*100000000000000^53 ≤ 45697699894859^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5479733297 10000000000 45697699894859 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136221611/250000000 : ℝ)^69 ≤ (45362843371569/100000000000000 : ℝ)^53 := by
    have hnat : (136221611 : ℕ)^69*100000000000000^53 ≤ 45362843371569^53*250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136221611 250000000 45362843371569 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1564895559/10000000000 : ℝ)^69 ≤ (893945672913/10000000000000 : ℝ)^53 := by
    have hnat : (1564895559 : ℕ)^69*10000000000000^53 ≤ 893945672913^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1564895559 10000000000 893945672913 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5479733297/10000000000 : ℝ), (136221611/250000000 : ℝ), (-1564895559/10000000000 : ℝ)] ![(45697699894859/100000000000000 : ℝ), (45362843371569/100000000000000 : ℝ), (893945672913/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5479733297/10000000000 : ℝ)|^69 ≤ (45697699894859/100000000000000 : ℝ)^53
        have hw : |(5479733297/10000000000 : ℝ)|=(5479733297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(136221611/250000000 : ℝ)|^69 ≤ (45362843371569/100000000000000 : ℝ)^53
        have hw : |(136221611/250000000 : ℝ)|=(136221611/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1564895559/10000000000 : ℝ)|^69 ≤ (893945672913/10000000000000 : ℝ)^53
        have hw : |(-1564895559/10000000000 : ℝ)|=(1564895559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308054_s1_s1_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-8852731/10000000000 : ℝ)*x 0 + (1784903361/10000000000 : ℝ)*x 1 + (-9173757707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8852731/10000000000 : ℝ)^69 ≤ (10603279677/100000000000000 : ℝ)^53 := by
    have hnat : (8852731 : ℕ)^69*100000000000000^53 ≤ 10603279677^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8852731 10000000000 10603279677 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1784903361/10000000000 : ℝ)^69 ≤ (5304654172943/50000000000000 : ℝ)^53 := by
    have hnat : (1784903361 : ℕ)^69*50000000000000^53 ≤ 5304654172943^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1784903361 10000000000 5304654172943 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9173757707/10000000000 : ℝ)^69 ≤ (89380088367173/100000000000000 : ℝ)^53 := by
    have hnat : (9173757707 : ℕ)^69*100000000000000^53 ≤ 89380088367173^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9173757707 10000000000 89380088367173 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-8852731/10000000000 : ℝ), (1784903361/10000000000 : ℝ), (-9173757707/10000000000 : ℝ)] ![(10603279677/100000000000000 : ℝ), (5304654172943/50000000000000 : ℝ), (89380088367173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-8852731/10000000000 : ℝ)|^69 ≤ (10603279677/100000000000000 : ℝ)^53
        have hw : |(-8852731/10000000000 : ℝ)|=(8852731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1784903361/10000000000 : ℝ)|^69 ≤ (5304654172943/50000000000000 : ℝ)^53
        have hw : |(1784903361/10000000000 : ℝ)|=(1784903361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-9173757707/10000000000 : ℝ)|^69 ≤ (89380088367173/100000000000000 : ℝ)^53
        have hw : |(-9173757707/10000000000 : ℝ)|=(9173757707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308054_s1_s1_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (471736323/1250000000 : ℝ)*x 0 + (-121593647/1250000000 : ℝ)*x 1 + (-1471501023/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (471736323/1250000000 : ℝ)^69 ≤ (175754965013/625000000000 : ℝ)^53 := by
    have hnat : (471736323 : ℕ)^69*625000000000^53 ≤ 175754965013^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471736323 1250000000 175754965013 625000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (121593647/1250000000 : ℝ)^69 ≤ (1203460136989/25000000000000 : ℝ)^53 := by
    have hnat : (121593647 : ℕ)^69*25000000000000^53 ≤ 1203460136989^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121593647 1250000000 1203460136989 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1471501023/2000000000 : ℝ)^69 ≤ (8383170628853/12500000000000 : ℝ)^53 := by
    have hnat : (1471501023 : ℕ)^69*12500000000000^53 ≤ 8383170628853^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1471501023 2000000000 8383170628853 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(471736323/1250000000 : ℝ), (-121593647/1250000000 : ℝ), (-1471501023/2000000000 : ℝ)] ![(175754965013/625000000000 : ℝ), (1203460136989/25000000000000 : ℝ), (8383170628853/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(471736323/1250000000 : ℝ)|^69 ≤ (175754965013/625000000000 : ℝ)^53
        have hw : |(471736323/1250000000 : ℝ)|=(471736323/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-121593647/1250000000 : ℝ)|^69 ≤ (1203460136989/25000000000000 : ℝ)^53
        have hw : |(-121593647/1250000000 : ℝ)|=(121593647/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1471501023/2000000000 : ℝ)|^69 ≤ (8383170628853/12500000000000 : ℝ)^53
        have hw : |(-1471501023/2000000000 : ℝ)|=(1471501023/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308054_s1_s1_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1577626673/5000000000 : ℝ)*x 0 + (322327573/400000000 : ℝ)*x 1 + (538386401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1577626673/5000000000 : ℝ)^69 ≤ (4454811006351/20000000000000 : ℝ)^53 := by
    have hnat : (1577626673 : ℕ)^69*20000000000000^53 ≤ 4454811006351^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1577626673 5000000000 4454811006351 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (322327573/400000000 : ℝ)^69 ≤ (15099473076717/20000000000000 : ℝ)^53 := by
    have hnat : (322327573 : ℕ)^69*20000000000000^53 ≤ 15099473076717^53*400000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322327573 400000000 15099473076717 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538386401/10000000000 : ℝ)^69 ≤ (557144891289/25000000000000 : ℝ)^53 := by
    have hnat : (538386401 : ℕ)^69*25000000000000^53 ≤ 557144891289^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538386401 10000000000 557144891289 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1577626673/5000000000 : ℝ), (322327573/400000000 : ℝ), (538386401/10000000000 : ℝ)] ![(4454811006351/20000000000000 : ℝ), (15099473076717/20000000000000 : ℝ), (557144891289/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1577626673/5000000000 : ℝ)|^69 ≤ (4454811006351/20000000000000 : ℝ)^53
        have hw : |(1577626673/5000000000 : ℝ)|=(1577626673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(322327573/400000000 : ℝ)|^69 ≤ (15099473076717/20000000000000 : ℝ)^53
        have hw : |(322327573/400000000 : ℝ)|=(322327573/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(538386401/10000000000 : ℝ)|^69 ≤ (557144891289/25000000000000 : ℝ)^53
        have hw : |(538386401/10000000000 : ℝ)|=(538386401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308054_s1_s1_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (450207137/1250000000 : ℝ)*x 0 + (7664338269/10000000000 : ℝ)*x 1 + (-32158339/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (450207137/1250000000 : ℝ)^69 ≤ (661540278667/2500000000000 : ℝ)^53 := by
    have hnat : (450207137 : ℕ)^69*2500000000000^53 ≤ 661540278667^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450207137 1250000000 661540278667 2500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7664338269/10000000000 : ℝ)^69 ≤ (35364628118603/50000000000000 : ℝ)^53 := by
    have hnat : (7664338269 : ℕ)^69*50000000000000^53 ≤ 35364628118603^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7664338269 10000000000 35364628118603 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32158339/500000000 : ℝ)^69 ≤ (35114157527/1250000000000 : ℝ)^53 := by
    have hnat : (32158339 : ℕ)^69*1250000000000^53 ≤ 35114157527^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32158339 500000000 35114157527 1250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(450207137/1250000000 : ℝ), (7664338269/10000000000 : ℝ), (-32158339/500000000 : ℝ)] ![(661540278667/2500000000000 : ℝ), (35364628118603/50000000000000 : ℝ), (35114157527/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(450207137/1250000000 : ℝ)|^69 ≤ (661540278667/2500000000000 : ℝ)^53
        have hw : |(450207137/1250000000 : ℝ)|=(450207137/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7664338269/10000000000 : ℝ)|^69 ≤ (35364628118603/50000000000000 : ℝ)^53
        have hw : |(7664338269/10000000000 : ℝ)|=(7664338269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-32158339/500000000 : ℝ)|^69 ≤ (35114157527/1250000000000 : ℝ)^53
        have hw : |(-32158339/500000000 : ℝ)|=(32158339/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308054_s1_s1_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (847557/1250000000 : ℝ)*x 0 + (516969053/2500000000 : ℝ)*x 1 + (-8996864629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (847557/1250000000 : ℝ)^69 ≤ (936629493/12500000000000 : ℝ)^53 := by
    have hnat : (847557 : ℕ)^69*12500000000000^53 ≤ 936629493^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847557 1250000000 936629493 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (516969053/2500000000 : ℝ)^69 ≤ (12849624462397/100000000000000 : ℝ)^53 := by
    have hnat : (516969053 : ℕ)^69*100000000000000^53 ≤ 12849624462397^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516969053 2500000000 12849624462397 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8996864629/10000000000 : ℝ)^69 ≤ (871428824877/1000000000000 : ℝ)^53 := by
    have hnat : (8996864629 : ℕ)^69*1000000000000^53 ≤ 871428824877^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8996864629 10000000000 871428824877 1000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(847557/1250000000 : ℝ), (516969053/2500000000 : ℝ), (-8996864629/10000000000 : ℝ)] ![(936629493/12500000000000 : ℝ), (12849624462397/100000000000000 : ℝ), (871428824877/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(847557/1250000000 : ℝ)|^69 ≤ (936629493/12500000000000 : ℝ)^53
        have hw : |(847557/1250000000 : ℝ)|=(847557/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(516969053/2500000000 : ℝ)|^69 ≤ (12849624462397/100000000000000 : ℝ)^53
        have hw : |(516969053/2500000000 : ℝ)|=(516969053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8996864629/10000000000 : ℝ)|^69 ≤ (871428824877/1000000000000 : ℝ)^53
        have hw : |(-8996864629/10000000000 : ℝ)|=(8996864629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308054_s1_s1_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3348651699/10000000000 : ℝ)*x 0 + (-75782841/312500000 : ℝ)*x 1 + (-6764952961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3348651699/10000000000 : ℝ)^69 ≤ (12033847509213/50000000000000 : ℝ)^53 := by
    have hnat : (3348651699 : ℕ)^69*50000000000000^53 ≤ 12033847509213^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3348651699 10000000000 12033847509213 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (75782841/312500000 : ℝ)^69 ≤ (7905807204923/50000000000000 : ℝ)^53 := by
    have hnat : (75782841 : ℕ)^69*50000000000000^53 ≤ 7905807204923^53*312500000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75782841 312500000 7905807204923 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6764952961/10000000000 : ℝ)^69 ≤ (15030172640463/25000000000000 : ℝ)^53 := by
    have hnat : (6764952961 : ℕ)^69*25000000000000^53 ≤ 15030172640463^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6764952961 10000000000 15030172640463 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3348651699/10000000000 : ℝ), (-75782841/312500000 : ℝ), (-6764952961/10000000000 : ℝ)] ![(12033847509213/50000000000000 : ℝ), (7905807204923/50000000000000 : ℝ), (15030172640463/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3348651699/10000000000 : ℝ)|^69 ≤ (12033847509213/50000000000000 : ℝ)^53
        have hw : |(3348651699/10000000000 : ℝ)|=(3348651699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-75782841/312500000 : ℝ)|^69 ≤ (7905807204923/50000000000000 : ℝ)^53
        have hw : |(-75782841/312500000 : ℝ)|=(75782841/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6764952961/10000000000 : ℝ)|^69 ≤ (15030172640463/25000000000000 : ℝ)^53
        have hw : |(-6764952961/10000000000 : ℝ)|=(6764952961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308054_s1_s1_16 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (504680447/625000000 : ℝ)*x 0 + (1380672711/5000000000 : ℝ)*x 1 + (1088816921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (504680447/625000000 : ℝ)^69 ≤ (3785054963249/5000000000000 : ℝ)^53 := by
    have hnat : (504680447 : ℕ)^69*5000000000000^53 ≤ 3785054963249^53*625000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504680447 625000000 3785054963249 5000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1380672711/5000000000 : ℝ)^69 ≤ (9362082695857/50000000000000 : ℝ)^53 := by
    have hnat : (1380672711 : ℕ)^69*50000000000000^53 ≤ 9362082695857^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380672711 5000000000 9362082695857 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1088816921/10000000000 : ℝ)^69 ≤ (696841916737/12500000000000 : ℝ)^53 := by
    have hnat : (1088816921 : ℕ)^69*12500000000000^53 ≤ 696841916737^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088816921 10000000000 696841916737 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(504680447/625000000 : ℝ), (1380672711/5000000000 : ℝ), (1088816921/10000000000 : ℝ)] ![(3785054963249/5000000000000 : ℝ), (9362082695857/50000000000000 : ℝ), (696841916737/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(504680447/625000000 : ℝ)|^69 ≤ (3785054963249/5000000000000 : ℝ)^53
        have hw : |(504680447/625000000 : ℝ)|=(504680447/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1380672711/5000000000 : ℝ)|^69 ≤ (9362082695857/50000000000000 : ℝ)^53
        have hw : |(1380672711/5000000000 : ℝ)|=(1380672711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1088816921/10000000000 : ℝ)|^69 ≤ (696841916737/12500000000000 : ℝ)^53
        have hw : |(1088816921/10000000000 : ℝ)|=(1088816921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308054_s1_s1_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7457717307/10000000000 : ℝ)*x 0 + (712910859/2000000000 : ℝ)*x 1 + (-1097952277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7457717307/10000000000 : ℝ)^69 ≤ (17064255082673/25000000000000 : ℝ)^53 := by
    have hnat : (7457717307 : ℕ)^69*25000000000000^53 ≤ 17064255082673^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7457717307 10000000000 17064255082673 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (712910859/2000000000 : ℝ)^69 ≤ (13053637125739/50000000000000 : ℝ)^53 := by
    have hnat : (712910859 : ℕ)^69*50000000000000^53 ≤ 13053637125739^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      712910859 2000000000 13053637125739 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1097952277/10000000000 : ℝ)^69 ≤ (5635705402109/100000000000000 : ℝ)^53 := by
    have hnat : (1097952277 : ℕ)^69*100000000000000^53 ≤ 5635705402109^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097952277 10000000000 5635705402109 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7457717307/10000000000 : ℝ), (712910859/2000000000 : ℝ), (-1097952277/10000000000 : ℝ)] ![(17064255082673/25000000000000 : ℝ), (13053637125739/50000000000000 : ℝ), (5635705402109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7457717307/10000000000 : ℝ)|^69 ≤ (17064255082673/25000000000000 : ℝ)^53
        have hw : |(7457717307/10000000000 : ℝ)|=(7457717307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(712910859/2000000000 : ℝ)|^69 ≤ (13053637125739/50000000000000 : ℝ)^53
        have hw : |(712910859/2000000000 : ℝ)|=(712910859/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1097952277/10000000000 : ℝ)|^69 ≤ (5635705402109/100000000000000 : ℝ)^53
        have hw : |(-1097952277/10000000000 : ℝ)|=(1097952277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308054_s1_s1_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (41012797/10000000000 : ℝ)*x 0 + (1625301237/2500000000 : ℝ)*x 1 + (-5214065627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41012797/10000000000 : ℝ)^69 ≤ (9754416429/12500000000000 : ℝ)^53 := by
    have hnat : (41012797 : ℕ)^69*12500000000000^53 ≤ 9754416429^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41012797 10000000000 9754416429 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1625301237/2500000000 : ℝ)^69 ≤ (7135907069591/12500000000000 : ℝ)^53 := by
    have hnat : (1625301237 : ℕ)^69*12500000000000^53 ≤ 7135907069591^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1625301237 2500000000 7135907069591 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5214065627/10000000000 : ℝ)^69 ≤ (21417354054433/50000000000000 : ℝ)^53 := by
    have hnat : (5214065627 : ℕ)^69*50000000000000^53 ≤ 21417354054433^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214065627 10000000000 21417354054433 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41012797/10000000000 : ℝ), (1625301237/2500000000 : ℝ), (-5214065627/10000000000 : ℝ)] ![(9754416429/12500000000000 : ℝ), (7135907069591/12500000000000 : ℝ), (21417354054433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41012797/10000000000 : ℝ)|^69 ≤ (9754416429/12500000000000 : ℝ)^53
        have hw : |(41012797/10000000000 : ℝ)|=(41012797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1625301237/2500000000 : ℝ)|^69 ≤ (7135907069591/12500000000000 : ℝ)^53
        have hw : |(1625301237/2500000000 : ℝ)|=(1625301237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5214065627/10000000000 : ℝ)|^69 ≤ (21417354054433/50000000000000 : ℝ)^53
        have hw : |(-5214065627/10000000000 : ℝ)|=(5214065627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308054_s1_s1_22 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8119594547/10000000000 : ℝ)*x 0 + (-1656052139/10000000000 : ℝ)*x 1 + (-278041281/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8119594547/10000000000 : ℝ)^69 ≤ (76247209905367/100000000000000 : ℝ)^53 := by
    have hnat : (8119594547 : ℕ)^69*100000000000000^53 ≤ 76247209905367^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8119594547 10000000000 76247209905367 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1656052139/10000000000 : ℝ)^69 ≤ (601454501727/6250000000000 : ℝ)^53 := by
    have hnat : (1656052139 : ℕ)^69*6250000000000^53 ≤ 601454501727^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1656052139 10000000000 601454501727 6250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (278041281/1250000000 : ℝ)^69 ≤ (14129518049811/100000000000000 : ℝ)^53 := by
    have hnat : (278041281 : ℕ)^69*100000000000000^53 ≤ 14129518049811^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278041281 1250000000 14129518049811 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8119594547/10000000000 : ℝ), (-1656052139/10000000000 : ℝ), (-278041281/1250000000 : ℝ)] ![(76247209905367/100000000000000 : ℝ), (601454501727/6250000000000 : ℝ), (14129518049811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8119594547/10000000000 : ℝ)|^69 ≤ (76247209905367/100000000000000 : ℝ)^53
        have hw : |(8119594547/10000000000 : ℝ)|=(8119594547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1656052139/10000000000 : ℝ)|^69 ≤ (601454501727/6250000000000 : ℝ)^53
        have hw : |(-1656052139/10000000000 : ℝ)|=(1656052139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-278041281/1250000000 : ℝ)|^69 ≤ (14129518049811/100000000000000 : ℝ)^53
        have hw : |(-278041281/1250000000 : ℝ)|=(278041281/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308054_s1_s1_23 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2975479563/10000000000 : ℝ)*x 0 + (3501214601/5000000000 : ℝ)*x 1 + (500706321/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2975479563/10000000000 : ℝ)^69 ≤ (20636249710201/100000000000000 : ℝ)^53 := by
    have hnat : (2975479563 : ℕ)^69*100000000000000^53 ≤ 20636249710201^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2975479563 10000000000 20636249710201 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3501214601/5000000000 : ℝ)^69 ≤ (62882726099871/100000000000000 : ℝ)^53 := by
    have hnat : (3501214601 : ℕ)^69*100000000000000^53 ≤ 62882726099871^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3501214601 5000000000 62882726099871 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (500706321/2000000000 : ℝ)^69 ≤ (8240512086611/50000000000000 : ℝ)^53 := by
    have hnat : (500706321 : ℕ)^69*50000000000000^53 ≤ 8240512086611^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500706321 2000000000 8240512086611 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2975479563/10000000000 : ℝ), (3501214601/5000000000 : ℝ), (500706321/2000000000 : ℝ)] ![(20636249710201/100000000000000 : ℝ), (62882726099871/100000000000000 : ℝ), (8240512086611/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2975479563/10000000000 : ℝ)|^69 ≤ (20636249710201/100000000000000 : ℝ)^53
        have hw : |(2975479563/10000000000 : ℝ)|=(2975479563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3501214601/5000000000 : ℝ)|^69 ≤ (62882726099871/100000000000000 : ℝ)^53
        have hw : |(3501214601/5000000000 : ℝ)|=(3501214601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(500706321/2000000000 : ℝ)|^69 ≤ (8240512086611/50000000000000 : ℝ)^53
        have hw : |(500706321/2000000000 : ℝ)|=(500706321/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308054_s1_s1_27 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7329967359/10000000000 : ℝ)*x 0 + (350668241/1000000000 : ℝ)*x 1 + (-1396006957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7329967359/10000000000 : ℝ)^69 ≤ (8342344907939/12500000000000 : ℝ)^53 := by
    have hnat : (7329967359 : ℕ)^69*12500000000000^53 ≤ 8342344907939^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7329967359 10000000000 8342344907939 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (350668241/1000000000 : ℝ)^69 ≤ (12778406033341/50000000000000 : ℝ)^53 := by
    have hnat : (350668241 : ℕ)^69*50000000000000^53 ≤ 12778406033341^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      350668241 1000000000 12778406033341 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1396006957/10000000000 : ℝ)^69 ≤ (1540885730587/20000000000000 : ℝ)^53 := by
    have hnat : (1396006957 : ℕ)^69*20000000000000^53 ≤ 1540885730587^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1396006957 10000000000 1540885730587 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7329967359/10000000000 : ℝ), (350668241/1000000000 : ℝ), (-1396006957/10000000000 : ℝ)] ![(8342344907939/12500000000000 : ℝ), (12778406033341/50000000000000 : ℝ), (1540885730587/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7329967359/10000000000 : ℝ)|^69 ≤ (8342344907939/12500000000000 : ℝ)^53
        have hw : |(7329967359/10000000000 : ℝ)|=(7329967359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(350668241/1000000000 : ℝ)|^69 ≤ (12778406033341/50000000000000 : ℝ)^53
        have hw : |(350668241/1000000000 : ℝ)|=(350668241/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1396006957/10000000000 : ℝ)|^69 ≤ (1540885730587/20000000000000 : ℝ)^53
        have hw : |(-1396006957/10000000000 : ℝ)|=(1396006957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308054_s1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((11281/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11281/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(46183/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(46183/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-16429/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-16429/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((77337/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(77337/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(82057/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(82057/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-67921/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-67921/100000 : ℝ)*X 1 2) := by
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
  have main1 : (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (3861/5000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (3861/5000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (11517/6250 : ℝ) := by
    linarith only [f.Tcap]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (11281/12500 : ℝ) ^ (17/4 : ℝ) ≤ (64656135227435885161/100000000000000000000 : ℝ) := by
    have hpowers : (11281/12500 : ℝ)^17 ≤ (64656135227435885161/100000000000000000000 : ℝ)^4 := by
      have hnat : (11281 : ℕ)^17*100000000000000000000^4 ≤ 64656135227435885161^4*12500^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11281 12500 64656135227435885161 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11281/12500 : ℝ)) (X := (64656135227435885161/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (164656135227435885161/100000000000000000000 : ℝ) ≤ (5622500650363889/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (164656135227435885161/100000000000000000000 : ℝ)^4 ≤ (5622500650363889/5000000000000000 : ℝ)^17 := by
      have hnat : (164656135227435885161 : ℕ)^4*5000000000000000^17 ≤ 5622500650363889^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        164656135227435885161 100000000000000000000 5622500650363889 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5622500650363889/5000000000000000 : ℝ)) (X := (164656135227435885161/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (114656135227435885161/50000000000000000000 : ℝ) ≤ (12156440316472123/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (114656135227435885161/50000000000000000000 : ℝ)^4 ≤ (12156440316472123/10000000000000000 : ℝ)^17 := by
      have hnat : (114656135227435885161 : ℕ)^4*10000000000000000^17 ≤ 12156440316472123^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        114656135227435885161 50000000000000000000 12156440316472123 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12156440316472123/10000000000000000 : ℝ)) (X := (114656135227435885161/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(622500650363889/4512400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(182287803148869/1804960000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (11281/12500 : ℝ)) (alpha := (622500650363889/4512400000000000 : ℝ)) (beta := (182287803148869/1804960000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (11281/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(622500650363889/4512400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(182287803148869/1804960000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (46183/50000 : ℝ) ^ (17/4 : ℝ) ≤ (35677678232124445147/50000000000000000000 : ℝ) := by
    have hpowers : (46183/50000 : ℝ)^17 ≤ (35677678232124445147/50000000000000000000 : ℝ)^4 := by
      have hnat : (46183 : ℕ)^17*50000000000000000000^4 ≤ 35677678232124445147^4*50000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        46183 50000 35677678232124445147 50000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (46183/50000 : ℝ)) (X := (35677678232124445147/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (85677678232124445147/50000000000000000000 : ℝ) ≤ (567550817660077/500000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (85677678232124445147/50000000000000000000 : ℝ)^4 ≤ (567550817660077/500000000000000 : ℝ)^17 := by
      have hnat : (85677678232124445147 : ℕ)^4*500000000000000^17 ≤ 567550817660077^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        85677678232124445147 50000000000000000000 567550817660077 500000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (567550817660077/500000000000000 : ℝ)) (X := (85677678232124445147/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (60677678232124445147/25000000000000000000 : ℝ) ≤ (12319956197889753/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (60677678232124445147/25000000000000000000 : ℝ)^4 ≤ (12319956197889753/10000000000000000 : ℝ)^17 := by
      have hnat : (60677678232124445147 : ℕ)^4*10000000000000000^17 ≤ 12319956197889753^17*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60677678232124445147 25000000000000000000 12319956197889753 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12319956197889753/10000000000000000 : ℝ)) (X := (60677678232124445147/25000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(67550817660077/461830000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(968939844688213/9236600000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (46183/50000 : ℝ)) (alpha := (67550817660077/461830000000000 : ℝ)) (beta := (968939844688213/9236600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (46183/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(67550817660077/461830000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(968939844688213/9236600000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (16429/20000 : ℝ) ^ (17/4 : ℝ) ≤ (43348075317247070933/100000000000000000000 : ℝ) := by
    have hpowers : (16429/20000 : ℝ)^17 ≤ (43348075317247070933/100000000000000000000 : ℝ)^4 := by
      have hnat : (16429 : ℕ)^17*100000000000000000000^4 ≤ 43348075317247070933^4*20000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16429 20000 43348075317247070933 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16429/20000 : ℝ)) (X := (43348075317247070933/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (143348075317247070933/100000000000000000000 : ℝ) ≤ (5442119707522659/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (143348075317247070933/100000000000000000000 : ℝ)^4 ≤ (5442119707522659/5000000000000000 : ℝ)^17 := by
      have hnat : (143348075317247070933 : ℕ)^4*5000000000000000^17 ≤ 5442119707522659^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        143348075317247070933 100000000000000000000 5442119707522659 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5442119707522659/5000000000000000 : ℝ)) (X := (143348075317247070933/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (93348075317247070933/50000000000000000000 : ℝ) ≤ (5791173288712231/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (93348075317247070933/50000000000000000000 : ℝ)^4 ≤ (5791173288712231/5000000000000000 : ℝ)^17 := by
      have hnat : (93348075317247070933 : ℕ)^4*5000000000000000^17 ≤ 5791173288712231^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        93348075317247070933 50000000000000000000 5791173288712231 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5791173288712231/5000000000000000 : ℝ)) (X := (93348075317247070933/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(442119707522659/4107250000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(12466199328199/146687500000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (16429/20000 : ℝ)) (alpha := (442119707522659/4107250000000000 : ℝ)) (beta := (12466199328199/146687500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (16429/20000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(442119707522659/4107250000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(12466199328199/146687500000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_1 : ((5921116991/10000000000 : ℝ)*X 1 0+(-367937637/2500000000 : ℝ)*X 1 1+(-5060531129/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308054_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((279871809/500000000 : ℝ)*X 2 0+(55528563/100000000 : ℝ)*X 2 1+(1229044127/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308054_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((5479733297/10000000000 : ℝ)*X 0 0+(136221611/250000000 : ℝ)*X 0 1+(-1564895559/10000000000 : ℝ)*X 0 2+(5479733297/10000000000 : ℝ)*X 1 0+(136221611/250000000 : ℝ)*X 1 1+(-1564895559/10000000000 : ℝ)*X 1 2+(5479733297/10000000000 : ℝ)*X 2 0+(136221611/250000000 : ℝ)*X 2 1+(-1564895559/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308054_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-8852731/10000000000 : ℝ)*X 0 0+(1784903361/10000000000 : ℝ)*X 0 1+(-9173757707/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308054_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((471736323/1250000000 : ℝ)*X 1 0+(-121593647/1250000000 : ℝ)*X 1 1+(-1471501023/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308054_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((1577626673/5000000000 : ℝ)*X 2 0+(322327573/400000000 : ℝ)*X 2 1+(538386401/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308054_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((450207137/1250000000 : ℝ)*X 0 0+(7664338269/10000000000 : ℝ)*X 0 1+(-32158339/500000000 : ℝ)*X 0 2+(450207137/1250000000 : ℝ)*X 1 0+(7664338269/10000000000 : ℝ)*X 1 1+(-32158339/500000000 : ℝ)*X 1 2+(450207137/1250000000 : ℝ)*X 2 0+(7664338269/10000000000 : ℝ)*X 2 1+(-32158339/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308054_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((847557/1250000000 : ℝ)*X 0 0+(516969053/2500000000 : ℝ)*X 0 1+(-8996864629/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308054_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((3348651699/10000000000 : ℝ)*X 1 0+(-75782841/312500000 : ℝ)*X 1 1+(-6764952961/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308054_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((504680447/625000000 : ℝ)*X 2 0+(1380672711/5000000000 : ℝ)*X 2 1+(1088816921/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308054_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((7457717307/10000000000 : ℝ)*X 0 0+(712910859/2000000000 : ℝ)*X 0 1+(-1097952277/10000000000 : ℝ)*X 0 2+(7457717307/10000000000 : ℝ)*X 1 0+(712910859/2000000000 : ℝ)*X 1 1+(-1097952277/10000000000 : ℝ)*X 1 2+(7457717307/10000000000 : ℝ)*X 2 0+(712910859/2000000000 : ℝ)*X 2 1+(-1097952277/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308054_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((41012797/10000000000 : ℝ)*X 0 0+(1625301237/2500000000 : ℝ)*X 0 1+(-5214065627/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308054_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((8119594547/10000000000 : ℝ)*X 1 0+(-1656052139/10000000000 : ℝ)*X 1 1+(-278041281/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308054_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((2975479563/10000000000 : ℝ)*X 2 0+(3501214601/5000000000 : ℝ)*X 2 1+(500706321/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308054_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((7329967359/10000000000 : ℝ)*X 0 0+(350668241/1000000000 : ℝ)*X 0 1+(-1396006957/10000000000 : ℝ)*X 0 2+(7329967359/10000000000 : ℝ)*X 1 0+(350668241/1000000000 : ℝ)*X 1 1+(-1396006957/10000000000 : ℝ)*X 1 2+(7329967359/10000000000 : ℝ)*X 2 0+(350668241/1000000000 : ℝ)*X 2 1+(-1396006957/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308054_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((77337/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(77337/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1395922040106220425539159889/189685126750000000000000000000000 : ℝ) := by norm_num
    linear_combination (676346054743/1000000000000 : ℝ)*(base7) + (218489/250000000000 : ℝ)*(base39) + (39086599/1000000000000 : ℝ)*(base53) + (197941298467/1000000000000 : ℝ)*(base60) + (910034459663/500000000000 : ℝ)*(major_s1_0) + (910034459663/500000000000 : ℝ)*(major_s1_1) + (1820029832727/1000000000000 : ℝ)*(major_s1_2) + (27772561/500000000000 : ℝ)*(sp_s1_1) + (1031445908223/500000000000 : ℝ)*(sp_s1_7) + (1031586062389/500000000000 : ℝ)*(sp_s1_8) + (2063279122643/1000000000000 : ℝ)*(sp_s1_9) + (1837763517031/1000000000000 : ℝ)*(sp_s1_13) + (174109799/500000000000 : ℝ)*(sp_s1_14) + (2473229/200000000000 : ℝ)*(sp_s1_15) + (72588591393/62500000000 : ℝ)*(f.failure) + (2063279122643/1000000000000 : ℝ)*(f.sum) + (61110400137046534681/189685126750000000000000000000000 : ℝ)*base62 + (96450696399983/586750000000000000000000000 : ℝ)*base64 + (625052840106301/4618300000000000000000000000 : ℝ)*base67 + (496032346970379/513406250000000000000000000 : ℝ)*base68 + (7531739118377222453/26476507000000000000000000000000 : ℝ)*base71 + (468874208618931/902480000000000000000000000 : ℝ)*base73 + (9135971603199/23091500000000000000000000 : ℝ)*base74 + (330399519435273/2256200000000000000000000000 : ℝ)*base76 + (57973325547299178611/208396169200000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (923/6250000000000000 : ℝ)*base87 + (923/6250000000000000 : ℝ)*base89 + (923/6250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(82057/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(82057/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (683890096176504402558592821/104198084600000000000000000000000 : ℝ) := by norm_num
    linear_combination (106535571217/125000000000 : ℝ)*(base7) + (198389/1000000000000 : ℝ)*(base40) + (282031706713/1000000000000 : ℝ)*(base53) + (37042693949/500000000000 : ℝ)*(base60) + (916688715431/500000000000 : ℝ)*(major_s1_0) + (916688715431/500000000000 : ℝ)*(major_s1_1) + (387836431037/250000000000 : ℝ)*(major_s1_2) + (14643/7812500000 : ℝ)*(sp_s1_1) + (12456017/500000000000 : ℝ)*(sp_s1_8) + (845651919691/500000000000 : ℝ)*(sp_s1_14) + (1691277053043/1000000000000 : ℝ)*(sp_s1_15) + (394667109219/200000000000 : ℝ)*(sp_s1_16) + (25277170059/12500000000 : ℝ)*(sp_s1_20) + (1301171/62500000000 : ℝ)*(sp_s1_27) + (1169909853719/1000000000000 : ℝ)*(f.failure) + (394667109219/200000000000 : ℝ)*(f.sum) + (63783409438135273647/94842563375000000000000000000000 : ℝ)*base62 + (32795287927951/73343750000000000000000000 : ℝ)*base65 + (2580456586203297/4618300000000000000000000000 : ℝ)*base67 + (220079293939807/4107250000000000000000000000 : ℝ)*base69 + (6671076478696518543/26476507000000000000000000000000 : ℝ)*base70 + (202667882863307/902480000000000000000000000 : ℝ)*base73 + (15407636774771/230915000000000000000000000 : ℝ)*base75 + (153779735606159/2256200000000000000000000000 : ℝ)*base77 + (66282008778148272853/208396169200000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (41791/100000000000000000 : ℝ)*base86 + (41791/100000000000000000 : ℝ)*base88 + (58209/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-67921/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-67921/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5772530831980476266025308797209/1222764522781000000000000000000000000 : ℝ) := by norm_num
    linear_combination (853088398993/1000000000000 : ℝ)*(base7) + (47254911681/250000000000 : ℝ)*(base39) + (35779/125000000000 : ℝ)*(base43) + (858745244121/500000000000 : ℝ)*(major_s1_0) + (171749020201/100000000000 : ℝ)*(major_s1_1) + (858745244121/500000000000 : ℝ)*(major_s1_2) + (1740949/200000000000 : ℝ)*(sp_s1_2) + (1618467/500000000000 : ℝ)*(sp_s1_6) + (2339881/200000000000 : ℝ)*(sp_s1_9) + (3654189/62500000000 : ℝ)*(sp_s1_20) + (1815017707481/1000000000000 : ℝ)*(sp_s1_21) + (113438624607/62500000000 : ℝ)*(sp_s1_22) + (1814997303331/1000000000000 : ℝ)*(sp_s1_23) + (1948987085973/1000000000000 : ℝ)*(sp_s1_27) + (1095960390937/1000000000000 : ℝ)*(f.failure) + (113438624607/62500000000 : ℝ)*(f.sum) + (22811959549529558263/94842563375000000000000000000000 : ℝ)*base62 + (40324984970509/293375000000000000000000000 : ℝ)*base64 + (220482610629081/923660000000000000000000000 : ℝ)*base66 + (1918056958741153/4107250000000000000000000000 : ℝ)*base69 + (1028330185685939817/26476507000000000000000000000000 : ℝ)*base70 + (711300883847083/902480000000000000000000000 : ℝ)*base72 + (26028332327361/230915000000000000000000000 : ℝ)*base75 + (440463533491771/2256200000000000000000000000 : ℝ)*base76 + (3005063627457295957/8335846768000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (71793/100000000000000000 : ℝ)*base86 + (71793/100000000000000000 : ℝ)*base88 + (71793/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((11281/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11281/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(46183/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(46183/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-16429/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-16429/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((77337/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(77337/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(82057/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(82057/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-67921/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-67921/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c308054_s1 p hpa hpb X hX hprev0

#print axioms solution

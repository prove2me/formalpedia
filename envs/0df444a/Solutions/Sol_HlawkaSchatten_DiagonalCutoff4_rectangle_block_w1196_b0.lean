-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1196_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:01:13.003256+00:00
-- url     : https://prove2.me/submissions/55597cf6-7fa8-4c6b-91fc-6ec617db7a6f

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
theorem support_rectangle_w1196_s0_0 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1874836877/10000000000 : ℝ)*x 0 + (6041933337/10000000000 : ℝ)*x 1 + (4787263627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1874836877/10000000000 : ℝ)^8389 ≤ (5459050273837/50000000000000 : ℝ)^6341 := by
    have hnat : (1874836877 : ℕ)^8389*50000000000000^6341 ≤ 5459050273837^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1874836877 10000000000 5459050273837 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6041933337/10000000000 : ℝ)^8389 ≤ (10269059846599/20000000000000 : ℝ)^6341 := by
    have hnat : (6041933337 : ℕ)^8389*20000000000000^6341 ≤ 10269059846599^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6041933337 10000000000 10269059846599 20000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4787263627/10000000000 : ℝ)^8389 ≤ (9434150049853/25000000000000 : ℝ)^6341 := by
    have hnat : (4787263627 : ℕ)^8389*25000000000000^6341 ≤ 9434150049853^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4787263627 10000000000 9434150049853 25000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1874836877/10000000000 : ℝ), (6041933337/10000000000 : ℝ), (4787263627/10000000000 : ℝ)] ![(5459050273837/50000000000000 : ℝ), (10269059846599/20000000000000 : ℝ), (9434150049853/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1874836877/10000000000 : ℝ)|^8389 ≤ (5459050273837/50000000000000 : ℝ)^6341
        have hw : |(-1874836877/10000000000 : ℝ)|=(1874836877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6041933337/10000000000 : ℝ)|^8389 ≤ (10269059846599/20000000000000 : ℝ)^6341
        have hw : |(6041933337/10000000000 : ℝ)|=(6041933337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4787263627/10000000000 : ℝ)|^8389 ≤ (9434150049853/25000000000000 : ℝ)^6341
        have hw : |(4787263627/10000000000 : ℝ)|=(4787263627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s0_1 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5513751207/10000000000 : ℝ)*x 0 + (-2593364291/10000000000 : ℝ)*x 1 + (4787263619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5513751207/10000000000 : ℝ)^8389 ≤ (22746282863717/50000000000000 : ℝ)^6341 := by
    have hnat : (5513751207 : ℕ)^8389*50000000000000^6341 ≤ 22746282863717^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5513751207 10000000000 22746282863717 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2593364291/10000000000 : ℝ)^8389 ≤ (167708341453/1000000000000 : ℝ)^6341 := by
    have hnat : (2593364291 : ℕ)^8389*1000000000000^6341 ≤ 167708341453^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2593364291 10000000000 167708341453 1000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4787263619/10000000000 : ℝ)^8389 ≤ (37736600115983/100000000000000 : ℝ)^6341 := by
    have hnat : (4787263619 : ℕ)^8389*100000000000000^6341 ≤ 37736600115983^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4787263619 10000000000 37736600115983 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5513751207/10000000000 : ℝ), (-2593364291/10000000000 : ℝ), (4787263619/10000000000 : ℝ)] ![(22746282863717/50000000000000 : ℝ), (167708341453/1000000000000 : ℝ), (37736600115983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5513751207/10000000000 : ℝ)|^8389 ≤ (22746282863717/50000000000000 : ℝ)^6341
        have hw : |(5513751207/10000000000 : ℝ)|=(5513751207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2593364291/10000000000 : ℝ)|^8389 ≤ (167708341453/1000000000000 : ℝ)^6341
        have hw : |(-2593364291/10000000000 : ℝ)|=(2593364291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4787263619/10000000000 : ℝ)|^8389 ≤ (37736600115983/100000000000000 : ℝ)^6341
        have hw : |(4787263619/10000000000 : ℝ)|=(4787263619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s0_2 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1378437799/2500000000 : ℝ)*x 0 + (4787263631/10000000000 : ℝ)*x 1 + (-259336429/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1378437799/2500000000 : ℝ)^8389 ≤ (22746282803681/50000000000000 : ℝ)^6341 := by
    have hnat : (1378437799 : ℕ)^8389*50000000000000^6341 ≤ 22746282803681^6341*2500000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378437799 2500000000 22746282803681 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4787263631/10000000000 : ℝ)^8389 ≤ (37736600241127/100000000000000 : ℝ)^6341 := by
    have hnat : (4787263631 : ℕ)^8389*100000000000000^6341 ≤ 37736600241127^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4787263631 10000000000 37736600241127 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (259336429/1000000000 : ℝ)^8389 ≤ (3354166827349/20000000000000 : ℝ)^6341 := by
    have hnat : (259336429 : ℕ)^8389*20000000000000^6341 ≤ 3354166827349^6341*1000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259336429 1000000000 3354166827349 20000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1378437799/2500000000 : ℝ), (4787263631/10000000000 : ℝ), (-259336429/1000000000 : ℝ)] ![(22746282803681/50000000000000 : ℝ), (37736600241127/100000000000000 : ℝ), (3354166827349/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1378437799/2500000000 : ℝ)|^8389 ≤ (22746282803681/50000000000000 : ℝ)^6341
        have hw : |(1378437799/2500000000 : ℝ)|=(1378437799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4787263631/10000000000 : ℝ)|^8389 ≤ (37736600241127/100000000000000 : ℝ)^6341
        have hw : |(4787263631/10000000000 : ℝ)|=(4787263631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-259336429/1000000000 : ℝ)|^8389 ≤ (3354166827349/20000000000000 : ℝ)^6341
        have hw : |(-259336429/1000000000 : ℝ)|=(259336429/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s0_3 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2098329217/5000000000 : ℝ)*x 0 + (3118707927/10000000000 : ℝ)*x 1 + (2820653319/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2098329217/5000000000 : ℝ)^8389 ≤ (6340740703043/20000000000000 : ℝ)^6341 := by
    have hnat : (2098329217 : ℕ)^8389*20000000000000^6341 ≤ 6340740703043^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098329217 5000000000 6340740703043 20000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3118707927/10000000000 : ℝ)^8389 ≤ (21406218066151/100000000000000 : ℝ)^6341 := by
    have hnat : (3118707927 : ℕ)^8389*100000000000000^6341 ≤ 21406218066151^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3118707927 10000000000 21406218066151 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2820653319/5000000000 : ℝ)^8389 ≤ (46890078403337/100000000000000 : ℝ)^6341 := by
    have hnat : (2820653319 : ℕ)^8389*100000000000000^6341 ≤ 46890078403337^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2820653319 5000000000 46890078403337 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2098329217/5000000000 : ℝ), (3118707927/10000000000 : ℝ), (2820653319/5000000000 : ℝ)] ![(6340740703043/20000000000000 : ℝ), (21406218066151/100000000000000 : ℝ), (46890078403337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2098329217/5000000000 : ℝ)|^8389 ≤ (6340740703043/20000000000000 : ℝ)^6341
        have hw : |(2098329217/5000000000 : ℝ)|=(2098329217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3118707927/10000000000 : ℝ)|^8389 ≤ (21406218066151/100000000000000 : ℝ)^6341
        have hw : |(3118707927/10000000000 : ℝ)|=(3118707927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2820653319/5000000000 : ℝ)|^8389 ≤ (46890078403337/100000000000000 : ℝ)^6341
        have hw : |(2820653319/5000000000 : ℝ)|=(2820653319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s0_4 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-93991273/500000000 : ℝ)*x 0 + (2409800683/5000000000 : ℝ)*x 1 + (6008454909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (93991273/500000000 : ℝ)^8389 ≤ (2739137711333/25000000000000 : ℝ)^6341 := by
    have hnat : (93991273 : ℕ)^8389*25000000000000^6341 ≤ 2739137711333^6341*500000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93991273 500000000 2739137711333 25000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2409800683/5000000000 : ℝ)^8389 ≤ (38074206304347/100000000000000 : ℝ)^6341 := by
    have hnat : (2409800683 : ℕ)^8389*100000000000000^6341 ≤ 38074206304347^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2409800683 5000000000 38074206304347 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6008454909/10000000000 : ℝ)^8389 ≤ (12742310707981/25000000000000 : ℝ)^6341 := by
    have hnat : (6008454909 : ℕ)^8389*25000000000000^6341 ≤ 12742310707981^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6008454909 10000000000 12742310707981 25000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-93991273/500000000 : ℝ), (2409800683/5000000000 : ℝ), (6008454909/10000000000 : ℝ)] ![(2739137711333/25000000000000 : ℝ), (38074206304347/100000000000000 : ℝ), (12742310707981/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-93991273/500000000 : ℝ)|^8389 ≤ (2739137711333/25000000000000 : ℝ)^6341
        have hw : |(-93991273/500000000 : ℝ)|=(93991273/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2409800683/5000000000 : ℝ)|^8389 ≤ (38074206304347/100000000000000 : ℝ)^6341
        have hw : |(2409800683/5000000000 : ℝ)|=(2409800683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6008454909/10000000000 : ℝ)|^8389 ≤ (12742310707981/25000000000000 : ℝ)^6341
        have hw : |(6008454909/10000000000 : ℝ)|=(6008454909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s0_5 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2586288083/5000000000 : ℝ)*x 0 + (-274434627/2000000000 : ℝ)*x 1 + (3004227367/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2586288083/5000000000 : ℝ)^8389 ≤ (41806198433891/100000000000000 : ℝ)^6341 := by
    have hnat : (2586288083 : ℕ)^8389*100000000000000^6341 ≤ 41806198433891^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586288083 5000000000 41806198433891 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (274434627/2000000000 : ℝ)^8389 ≤ (1444912138211/20000000000000 : ℝ)^6341 := by
    have hnat : (274434627 : ℕ)^8389*20000000000000^6341 ≤ 1444912138211^6341*2000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274434627 2000000000 1444912138211 20000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3004227367/5000000000 : ℝ)^8389 ≤ (50969240867949/100000000000000 : ℝ)^6341 := by
    have hnat : (3004227367 : ℕ)^8389*100000000000000^6341 ≤ 50969240867949^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3004227367 5000000000 50969240867949 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2586288083/5000000000 : ℝ), (-274434627/2000000000 : ℝ), (3004227367/5000000000 : ℝ)] ![(41806198433891/100000000000000 : ℝ), (1444912138211/20000000000000 : ℝ), (50969240867949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2586288083/5000000000 : ℝ)|^8389 ≤ (41806198433891/100000000000000 : ℝ)^6341
        have hw : |(2586288083/5000000000 : ℝ)|=(2586288083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-274434627/2000000000 : ℝ)|^8389 ≤ (1444912138211/20000000000000 : ℝ)^6341
        have hw : |(-274434627/2000000000 : ℝ)|=(274434627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3004227367/5000000000 : ℝ)|^8389 ≤ (50969240867949/100000000000000 : ℝ)^6341
        have hw : |(3004227367/5000000000 : ℝ)|=(3004227367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s0_6 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2586288067/5000000000 : ℝ)*x 0 + (1502113709/2500000000 : ℝ)*x 1 + (-1372173019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2586288067/5000000000 : ℝ)^8389 ≤ (1672247923669/4000000000000 : ℝ)^6341 := by
    have hnat : (2586288067 : ℕ)^8389*4000000000000^6341 ≤ 1672247923669^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586288067 5000000000 1672247923669 4000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1502113709/2500000000 : ℝ)^8389 ≤ (25484621006333/50000000000000 : ℝ)^6341 := by
    have hnat : (1502113709 : ℕ)^8389*50000000000000^6341 ≤ 25484621006333^6341*2500000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1502113709 2500000000 25484621006333 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1372173019/10000000000 : ℝ)^8389 ≤ (1806139970763/25000000000000 : ℝ)^6341 := by
    have hnat : (1372173019 : ℕ)^8389*25000000000000^6341 ≤ 1806139970763^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372173019 10000000000 1806139970763 25000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2586288067/5000000000 : ℝ), (1502113709/2500000000 : ℝ), (-1372173019/10000000000 : ℝ)] ![(1672247923669/4000000000000 : ℝ), (25484621006333/50000000000000 : ℝ), (1806139970763/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2586288067/5000000000 : ℝ)|^8389 ≤ (1672247923669/4000000000000 : ℝ)^6341
        have hw : |(2586288067/5000000000 : ℝ)|=(2586288067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1502113709/2500000000 : ℝ)|^8389 ≤ (25484621006333/50000000000000 : ℝ)^6341
        have hw : |(1502113709/2500000000 : ℝ)|=(1502113709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1372173019/10000000000 : ℝ)|^8389 ≤ (1806139970763/25000000000000 : ℝ)^6341
        have hw : |(-1372173019/10000000000 : ℝ)|=(1372173019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s0_7 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (841337661/2000000000 : ℝ)*x 0 + (5576289191/10000000000 : ℝ)*x 1 + (637203751/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (841337661/2000000000 : ℝ)^8389 ≤ (3975498151033/12500000000000 : ℝ)^6341 := by
    have hnat : (841337661 : ℕ)^8389*12500000000000^6341 ≤ 3975498151033^6341*2000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      841337661 2000000000 3975498151033 12500000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5576289191/10000000000 : ℝ)^8389 ≤ (23088224752663/50000000000000 : ℝ)^6341 := by
    have hnat : (5576289191 : ℕ)^8389*50000000000000^6341 ≤ 23088224752663^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5576289191 10000000000 23088224752663 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (637203751/2000000000 : ℝ)^8389 ≤ (11009782636111/50000000000000 : ℝ)^6341 := by
    have hnat : (637203751 : ℕ)^8389*50000000000000^6341 ≤ 11009782636111^6341*2000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      637203751 2000000000 11009782636111 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(841337661/2000000000 : ℝ), (5576289191/10000000000 : ℝ), (637203751/2000000000 : ℝ)] ![(3975498151033/12500000000000 : ℝ), (23088224752663/50000000000000 : ℝ), (11009782636111/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(841337661/2000000000 : ℝ)|^8389 ≤ (3975498151033/12500000000000 : ℝ)^6341
        have hw : |(841337661/2000000000 : ℝ)|=(841337661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5576289191/10000000000 : ℝ)|^8389 ≤ (23088224752663/50000000000000 : ℝ)^6341
        have hw : |(5576289191/10000000000 : ℝ)|=(5576289191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(637203751/2000000000 : ℝ)|^8389 ≤ (11009782636111/50000000000000 : ℝ)^6341
        have hw : |(637203751/2000000000 : ℝ)|=(637203751/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1196_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150528399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (317/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27609/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (2097/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2097 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2097*1^512 ≤ 0^512*1^2097 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2097 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2097/512 : ℝ) ≤ (234507028104162603/10000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2097 ≤ (234507028104162603/10000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2097*10000000000000000000^512 ≤ 234507028104162603^512*5^2097 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 234507028104162603 10000000000000000000 2097 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (234507028104162603/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2097/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2097 := by
      have hnat : (1 : ℕ)^512*1^2097 ≤ 1^2097*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (10234507028104162603/10000000000000000000 : ℝ) ≤ (5028378128595073/5000000000000000 : ℝ) ^ (2097/512 : ℝ) := by
    have hpowers : (10234507028104162603/10000000000000000000 : ℝ)^512 ≤ (5028378128595073/5000000000000000 : ℝ)^2097 := by
      have hnat : (10234507028104162603 : ℕ)^512*5000000000000000^2097 ≤ 5028378128595073^2097*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10234507028104162603 10000000000000000000 5028378128595073 5000000000000000 512 2097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5028378128595073/5000000000000000 : ℝ)) (X := (10234507028104162603/10000000000000000000 : ℝ)) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (5234507028104162603/5000000000000000000 : ℝ) ≤ (2528378128595073/2500000000000000 : ℝ) ^ (2097/512 : ℝ) := by
    have hpowers : (5234507028104162603/5000000000000000000 : ℝ)^512 ≤ (2528378128595073/2500000000000000 : ℝ)^2097 := by
      have hnat : (5234507028104162603 : ℕ)^512*2500000000000000^2097 ≤ 2528378128595073^2097*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5234507028104162603 5000000000000000000 2528378128595073 2500000000000000 512 2097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2528378128595073/2500000000000000 : ℝ)) (X := (5234507028104162603/5000000000000000000 : ℝ)) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(28378128595073/2000000000000000 : ℝ)*(0 : ℝ))^(2097/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(28378128595073/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(234507028104162603/10000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(28378128595073/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2097/512 : ℝ) := by
    rw [show (1 : ℝ)+(28378128595073/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5028378128595073/5000000000000000 : ℝ) by norm_num, show 1+(234507028104162603/10000000000000000000 : ℝ)+(0 : ℝ)=(10234507028104162603/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(234507028104162603/10000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(28378128595073/2000000000000000 : ℝ)*(2/5 : ℝ))^(2097/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(28378128595073/2000000000000000 : ℝ)*(2/5 : ℝ)=(2528378128595073/2500000000000000 : ℝ) by norm_num, show 1+2*(234507028104162603/10000000000000000000 : ℝ)=(5234507028104162603/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(28378128595073/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2097/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28378128595073/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(28378128595073/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2097/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28378128595073/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(28378128595073/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2097/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28378128595073/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1874836877/10000000000 : ℝ)*X 0 0+(6041933337/10000000000 : ℝ)*X 0 1+(4787263627/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5513751207/10000000000 : ℝ)*X 1 0+(-2593364291/10000000000 : ℝ)*X 1 1+(4787263619/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1378437799/2500000000 : ℝ)*X 2 0+(4787263631/10000000000 : ℝ)*X 2 1+(-259336429/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2098329217/5000000000 : ℝ)*X 0 0+(3118707927/10000000000 : ℝ)*X 0 1+(2820653319/5000000000 : ℝ)*X 0 2+(2098329217/5000000000 : ℝ)*X 1 0+(3118707927/10000000000 : ℝ)*X 1 1+(2820653319/5000000000 : ℝ)*X 1 2+(2098329217/5000000000 : ℝ)*X 2 0+(3118707927/10000000000 : ℝ)*X 2 1+(2820653319/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-93991273/500000000 : ℝ)*X 0 0+(2409800683/5000000000 : ℝ)*X 0 1+(6008454909/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2586288083/5000000000 : ℝ)*X 1 0+(-274434627/2000000000 : ℝ)*X 1 1+(3004227367/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2586288067/5000000000 : ℝ)*X 2 0+(1502113709/2500000000 : ℝ)*X 2 1+(-1372173019/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((841337661/2000000000 : ℝ)*X 0 0+(5576289191/10000000000 : ℝ)*X 0 1+(637203751/2000000000 : ℝ)*X 0 2+(841337661/2000000000 : ℝ)*X 1 0+(5576289191/10000000000 : ℝ)*X 1 1+(637203751/2000000000 : ℝ)*X 1 2+(841337661/2000000000 : ℝ)*X 2 0+(5576289191/10000000000 : ℝ)*X 2 1+(637203751/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17621836757854183411029/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7685529/25000000000000 : ℝ)*(base1) + (173421259/25000000000000 : ℝ)*(base19) + (644611463/100000000000000 : ℝ)*(base23) + (5935437/12500000000000 : ℝ)*(base24) + (158620147/100000000000000 : ℝ)*(upper3) + (149180625618241/25000000000000 : ℝ)*(major0) + (149180625618241/25000000000000 : ℝ)*(major1) + (149180625618241/25000000000000 : ℝ)*(major2) + (797024851430513/100000000000000 : ℝ)*(sp0) + (398512831706037/50000000000000 : ℝ)*(sp1) + (15940513300043/2000000000000 : ℝ)*(sp2) + (396417309273219/100000000000000 : ℝ)*(sp3) + (1536408713/100000000000000 : ℝ)*(sp4) + (303462587/25000000000000 : ℝ)*(sp7) + (198209276932841/50000000000000 : ℝ)*(f.failure) + (797026357097109/100000000000000 : ℝ)*(f.sum) + (21333586098407/25000000000000000000000000000 : ℝ)*base66 + (429884094473407/50000000000000000000000000000 : ℝ)*base68 + (187822489973407/50000000000000000000000000000 : ℝ)*base70 + (247055253673407/50000000000000000000000000000 : ℝ)*base72 + (10794777148407/25000000000000000000000000000 : ℝ)*base74 + (368195641873407/50000000000000000000000000000 : ℝ)*base76 + (304515157773407/50000000000000000000000000000 : ℝ)*base78 + (14333735023407/50000000000000000000000000000 : ℝ)*base80 + (4451847476593/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (13748441/5000000000000000000000 : ℝ)*base90 + (13748441/5000000000000000000000 : ℝ)*base92 + (13748441/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12965051507033553228033/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13372719/50000000000000 : ℝ)*(base1) + (133537529/20000000000000 : ℝ)*(base19) + (166262771/25000000000000 : ℝ)*(base23) + (13777957/20000000000000 : ℝ)*(upper3) + (16250227/20000000000000 : ℝ)*(upper5) + (31487733508507/5000000000000 : ℝ)*(major0) + (31487733508507/5000000000000 : ℝ)*(major1) + (31487733508507/5000000000000 : ℝ)*(major2) + (85383247/6250000000000 : ℝ)*(sp1) + (702526413/50000000000000 : ℝ)*(sp2) + (841146583411003/100000000000000 : ℝ)*(sp4) + (841144522845969/100000000000000 : ℝ)*(sp5) + (168228897312331/20000000000000 : ℝ)*(sp6) + (418362670495593/100000000000000 : ℝ)*(sp7) + (41836269724103/10000000000000 : ℝ)*(f.failure) + (420573278332783/50000000000000 : ℝ)*(f.sum) + (11941013638989/5000000000000000000000000000 : ℝ)*base66 + (27795649823989/10000000000000000000000000000 : ℝ)*base68 + (66948899366011/10000000000000000000000000000 : ℝ)*base69 + (5492804043989/10000000000000000000000000000 : ℝ)*base72 + (30939328293989/5000000000000000000000000000 : ℝ)*base74 + (5190678703989/10000000000000000000000000000 : ℝ)*base76 + (2773388476011/10000000000000000000000000000 : ℝ)*base77 + (36781803296011/10000000000000000000000000000 : ℝ)*base79 + (6477620136011/5000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (3698903/1000000000000000000000 : ℝ)*base90 + (3698903/1000000000000000000000 : ℝ)*base92 + (3698903/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1196_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150528399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (317/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27609/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1196_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1196_s1_0 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-103779709/500000000 : ℝ)*x 0 + (5687306089/10000000000 : ℝ)*x 1 + (9791759/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103779709/500000000 : ℝ)^8389 ≤ (2498186453073/20000000000000 : ℝ)^6341 := by
    have hnat : (103779709 : ℕ)^8389*20000000000000^6341 ≤ 2498186453073^6341*500000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103779709 500000000 2498186453073 20000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5687306089/10000000000 : ℝ)^8389 ≤ (47396575302623/100000000000000 : ℝ)^6341 := by
    have hnat : (5687306089 : ℕ)^8389*100000000000000^6341 ≤ 47396575302623^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5687306089 10000000000 47396575302623 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9791759/19531250 : ℝ)^8389 ≤ (40112492415043/100000000000000 : ℝ)^6341 := by
    have hnat : (9791759 : ℕ)^8389*100000000000000^6341 ≤ 40112492415043^6341*19531250^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9791759 19531250 40112492415043 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-103779709/500000000 : ℝ), (5687306089/10000000000 : ℝ), (9791759/19531250 : ℝ)] ![(2498186453073/20000000000000 : ℝ), (47396575302623/100000000000000 : ℝ), (40112492415043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-103779709/500000000 : ℝ)|^8389 ≤ (2498186453073/20000000000000 : ℝ)^6341
        have hw : |(-103779709/500000000 : ℝ)|=(103779709/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5687306089/10000000000 : ℝ)|^8389 ≤ (47396575302623/100000000000000 : ℝ)^6341
        have hw : |(5687306089/10000000000 : ℝ)|=(5687306089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9791759/19531250 : ℝ)|^8389 ≤ (40112492415043/100000000000000 : ℝ)^6341
        have hw : |(9791759/19531250 : ℝ)|=(9791759/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s1_1 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1354040503/2500000000 : ℝ)*x 0 + (-2438293649/10000000000 : ℝ)*x 1 + (5013380959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1354040503/2500000000 : ℝ)^8389 ≤ (22215191368063/50000000000000 : ℝ)^6341 := by
    have hnat : (1354040503 : ℕ)^8389*50000000000000^6341 ≤ 22215191368063^6341*2500000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354040503 2500000000 22215191368063 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2438293649/10000000000 : ℝ)^8389 ≤ (15457121122697/100000000000000 : ℝ)^6341 := by
    have hnat : (2438293649 : ℕ)^8389*100000000000000^6341 ≤ 15457121122697^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2438293649 10000000000 15457121122697 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5013380959/10000000000 : ℝ)^8389 ≤ (10028124032617/25000000000000 : ℝ)^6341 := by
    have hnat : (5013380959 : ℕ)^8389*25000000000000^6341 ≤ 10028124032617^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5013380959 10000000000 10028124032617 25000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1354040503/2500000000 : ℝ), (-2438293649/10000000000 : ℝ), (5013380959/10000000000 : ℝ)] ![(22215191368063/50000000000000 : ℝ), (15457121122697/100000000000000 : ℝ), (10028124032617/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1354040503/2500000000 : ℝ)|^8389 ≤ (22215191368063/50000000000000 : ℝ)^6341
        have hw : |(1354040503/2500000000 : ℝ)|=(1354040503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2438293649/10000000000 : ℝ)|^8389 ≤ (15457121122697/100000000000000 : ℝ)^6341
        have hw : |(-2438293649/10000000000 : ℝ)|=(2438293649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5013380959/10000000000 : ℝ)|^8389 ≤ (10028124032617/25000000000000 : ℝ)^6341
        have hw : |(5013380959/10000000000 : ℝ)|=(5013380959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s1_2 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5416160981/10000000000 : ℝ)*x 0 + (5013381627/10000000000 : ℝ)*x 1 + (-121914707/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5416160981/10000000000 : ℝ)^8389 ≤ (22215185773457/50000000000000 : ℝ)^6341 := by
    have hnat : (5416160981 : ℕ)^8389*50000000000000^6341 ≤ 22215185773457^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416160981 10000000000 22215185773457 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5013381627/10000000000 : ℝ)^8389 ≤ (2005625160071/5000000000000 : ℝ)^6341 := by
    have hnat : (5013381627 : ℕ)^8389*5000000000000^6341 ≤ 2005625160071^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5013381627 10000000000 2005625160071 5000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (121914707/500000000 : ℝ)^8389 ≤ (3864281310151/25000000000000 : ℝ)^6341 := by
    have hnat : (121914707 : ℕ)^8389*25000000000000^6341 ≤ 3864281310151^6341*500000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121914707 500000000 3864281310151 25000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5416160981/10000000000 : ℝ), (5013381627/10000000000 : ℝ), (-121914707/500000000 : ℝ)] ![(22215185773457/50000000000000 : ℝ), (2005625160071/5000000000000 : ℝ), (3864281310151/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5416160981/10000000000 : ℝ)|^8389 ≤ (22215185773457/50000000000000 : ℝ)^6341
        have hw : |(5416160981/10000000000 : ℝ)|=(5416160981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5013381627/10000000000 : ℝ)|^8389 ≤ (2005625160071/5000000000000 : ℝ)^6341
        have hw : |(5013381627/10000000000 : ℝ)|=(5013381627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-121914707/500000000 : ℝ)|^8389 ≤ (3864281310151/25000000000000 : ℝ)^6341
        have hw : |(-121914707/500000000 : ℝ)|=(121914707/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s1_3 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4312832117/10000000000 : ℝ)*x 0 + (5899349/16000000 : ℝ)*x 1 + (201682659/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4312832117/10000000000 : ℝ)^8389 ≤ (32869953845739/100000000000000 : ℝ)^6341 := by
    have hnat : (4312832117 : ℕ)^8389*100000000000000^6341 ≤ 32869953845739^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4312832117 10000000000 32869953845739 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5899349/16000000 : ℝ)^8389 ≤ (13356813116443/50000000000000 : ℝ)^6341 := by
    have hnat : (5899349 : ℕ)^8389*50000000000000^6341 ≤ 13356813116443^6341*16000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5899349 16000000 13356813116443 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (201682659/400000000 : ℝ)^8389 ≤ (20208209953481/50000000000000 : ℝ)^6341 := by
    have hnat : (201682659 : ℕ)^8389*50000000000000^6341 ≤ 20208209953481^6341*400000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201682659 400000000 20208209953481 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4312832117/10000000000 : ℝ), (5899349/16000000 : ℝ), (201682659/400000000 : ℝ)] ![(32869953845739/100000000000000 : ℝ), (13356813116443/50000000000000 : ℝ), (20208209953481/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4312832117/10000000000 : ℝ)|^8389 ≤ (32869953845739/100000000000000 : ℝ)^6341
        have hw : |(4312832117/10000000000 : ℝ)|=(4312832117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5899349/16000000 : ℝ)|^8389 ≤ (13356813116443/50000000000000 : ℝ)^6341
        have hw : |(5899349/16000000 : ℝ)|=(5899349/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(201682659/400000000 : ℝ)|^8389 ≤ (20208209953481/50000000000000 : ℝ)^6341
        have hw : |(201682659/400000000 : ℝ)|=(201682659/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s1_4 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2076326987/10000000000 : ℝ)*x 0 + (313899573/625000000 : ℝ)*x 1 + (567811917/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2076326987/10000000000 : ℝ)^8389 ≤ (3124191743649/25000000000000 : ℝ)^6341 := by
    have hnat : (2076326987 : ℕ)^8389*25000000000000^6341 ≤ 3124191743649^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2076326987 10000000000 3124191743649 25000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (313899573/625000000 : ℝ)^8389 ≤ (1256497511387/3125000000000 : ℝ)^6341 := by
    have hnat : (313899573 : ℕ)^8389*3125000000000^6341 ≤ 1256497511387^6341*625000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      313899573 625000000 1256497511387 3125000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (567811917/1000000000 : ℝ)^8389 ≤ (47295312639989/100000000000000 : ℝ)^6341 := by
    have hnat : (567811917 : ℕ)^8389*100000000000000^6341 ≤ 47295312639989^6341*1000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      567811917 1000000000 47295312639989 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2076326987/10000000000 : ℝ), (313899573/625000000 : ℝ), (567811917/1000000000 : ℝ)] ![(3124191743649/25000000000000 : ℝ), (1256497511387/3125000000000 : ℝ), (47295312639989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2076326987/10000000000 : ℝ)|^8389 ≤ (3124191743649/25000000000000 : ℝ)^6341
        have hw : |(-2076326987/10000000000 : ℝ)|=(2076326987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(313899573/625000000 : ℝ)|^8389 ≤ (1256497511387/3125000000000 : ℝ)^6341
        have hw : |(313899573/625000000 : ℝ)|=(313899573/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(567811917/1000000000 : ℝ)|^8389 ≤ (47295312639989/100000000000000 : ℝ)^6341
        have hw : |(567811917/1000000000 : ℝ)|=(567811917/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s1_5 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2621459701/5000000000 : ℝ)*x 0 + (-55423623/312500000 : ℝ)*x 1 + (709764853/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2621459701/5000000000 : ℝ)^8389 ≤ (42560002340907/100000000000000 : ℝ)^6341 := by
    have hnat : (2621459701 : ℕ)^8389*100000000000000^6341 ≤ 42560002340907^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621459701 5000000000 42560002340907 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (55423623/312500000 : ℝ)^8389 ≤ (10144688809827/100000000000000 : ℝ)^6341 := by
    have hnat : (55423623 : ℕ)^8389*100000000000000^6341 ≤ 10144688809827^6341*312500000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55423623 312500000 10144688809827 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (709764853/1250000000 : ℝ)^8389 ≤ (23647654413603/50000000000000 : ℝ)^6341 := by
    have hnat : (709764853 : ℕ)^8389*50000000000000^6341 ≤ 23647654413603^6341*1250000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      709764853 1250000000 23647654413603 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2621459701/5000000000 : ℝ), (-55423623/312500000 : ℝ), (709764853/1250000000 : ℝ)] ![(42560002340907/100000000000000 : ℝ), (10144688809827/100000000000000 : ℝ), (23647654413603/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2621459701/5000000000 : ℝ)|^8389 ≤ (42560002340907/100000000000000 : ℝ)^6341
        have hw : |(2621459701/5000000000 : ℝ)|=(2621459701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-55423623/312500000 : ℝ)|^8389 ≤ (10144688809827/100000000000000 : ℝ)^6341
        have hw : |(-55423623/312500000 : ℝ)|=(55423623/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(709764853/1250000000 : ℝ)|^8389 ≤ (23647654413603/50000000000000 : ℝ)^6341
        have hw : |(709764853/1250000000 : ℝ)|=(709764853/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s1_6 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5242919389/10000000000 : ℝ)*x 0 + (709764929/1250000000 : ℝ)*x 1 + (-1773555069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5242919389/10000000000 : ℝ)^8389 ≤ (21280001100647/50000000000000 : ℝ)^6341 := by
    have hnat : (5242919389 : ℕ)^8389*50000000000000^6341 ≤ 21280001100647^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242919389 10000000000 21280001100647 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (709764929/1250000000 : ℝ)^8389 ≤ (23647657763563/50000000000000 : ℝ)^6341 := by
    have hnat : (709764929 : ℕ)^8389*50000000000000^6341 ≤ 23647657763563^6341*1250000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      709764929 1250000000 23647657763563 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1773555069/10000000000 : ℝ)^8389 ≤ (10144682248897/100000000000000 : ℝ)^6341 := by
    have hnat : (1773555069 : ℕ)^8389*100000000000000^6341 ≤ 10144682248897^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1773555069 10000000000 10144682248897 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5242919389/10000000000 : ℝ), (709764929/1250000000 : ℝ), (-1773555069/10000000000 : ℝ)] ![(21280001100647/50000000000000 : ℝ), (23647657763563/50000000000000 : ℝ), (10144682248897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5242919389/10000000000 : ℝ)|^8389 ≤ (21280001100647/50000000000000 : ℝ)^6341
        have hw : |(5242919389/10000000000 : ℝ)|=(5242919389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(709764929/1250000000 : ℝ)|^8389 ≤ (23647657763563/50000000000000 : ℝ)^6341
        have hw : |(709764929/1250000000 : ℝ)|=(709764929/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1773555069/10000000000 : ℝ)|^8389 ≤ (10144682248897/100000000000000 : ℝ)^6341
        have hw : |(-1773555069/10000000000 : ℝ)|=(1773555069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s1_7 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2157152801/5000000000 : ℝ)*x 0 + (1004789173/2000000000 : ℝ)*x 1 + (3705564567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157152801/5000000000 : ℝ)^8389 ≤ (16442405893899/50000000000000 : ℝ)^6341 := by
    have hnat : (2157152801 : ℕ)^8389*50000000000000^6341 ≤ 16442405893899^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157152801 5000000000 16442405893899 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1004789173/2000000000 : ℝ)^8389 ≤ (40224366419399/100000000000000 : ℝ)^6341 := by
    have hnat : (1004789173 : ℕ)^8389*100000000000000^6341 ≤ 40224366419399^6341*2000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004789173 2000000000 40224366419399 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3705564567/10000000000 : ℝ)^8389 ≤ (26890821776249/100000000000000 : ℝ)^6341 := by
    have hnat : (3705564567 : ℕ)^8389*100000000000000^6341 ≤ 26890821776249^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3705564567 10000000000 26890821776249 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2157152801/5000000000 : ℝ), (1004789173/2000000000 : ℝ), (3705564567/10000000000 : ℝ)] ![(16442405893899/50000000000000 : ℝ), (40224366419399/100000000000000 : ℝ), (26890821776249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2157152801/5000000000 : ℝ)|^8389 ≤ (16442405893899/50000000000000 : ℝ)^6341
        have hw : |(2157152801/5000000000 : ℝ)|=(2157152801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1004789173/2000000000 : ℝ)|^8389 ≤ (40224366419399/100000000000000 : ℝ)^6341
        have hw : |(1004789173/2000000000 : ℝ)|=(1004789173/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3705564567/10000000000 : ℝ)|^8389 ≤ (26890821776249/100000000000000 : ℝ)^6341
        have hw : |(3705564567/10000000000 : ℝ)|=(3705564567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1196_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150528399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27609/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (317/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5947/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20197/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27609/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (317/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27609/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (317/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27609/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (317/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27609/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (317/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27609/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (317/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27609/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (317/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (317/50000 : ℝ) ^ (2097/512 : ℝ) ≤ (49771428921/50000000000000000000 : ℝ) := by
    have hpowers : (317/50000 : ℝ)^2097 ≤ (49771428921/50000000000000000000 : ℝ)^512 := by
      have hnat : (317 : ℕ)^2097*50000000000000000000^512 ≤ 49771428921^512*50000^2097 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        317 50000 49771428921 50000000000000000000 2097 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (317/50000 : ℝ)) (X := (49771428921/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have hpowhi : (27609/100000 : ℝ) ^ (2097/512 : ℝ) ≤ (513699934126012927/100000000000000000000 : ℝ) := by
    have hpowers : (27609/100000 : ℝ)^2097 ≤ (513699934126012927/100000000000000000000 : ℝ)^512 := by
      have hnat : (27609 : ℕ)^2097*100000000000000000000^512 ≤ 513699934126012927^512*100000^2097 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27609 100000 513699934126012927 100000000000000000000 2097 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27609/100000 : ℝ)) (X := (513699934126012927/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000049771428921/25000000000000000000 : ℝ) ≤ (2500000001215211/2500000000000000 : ℝ) ^ (2097/512 : ℝ) := by
    have hpowers : (25000000049771428921/25000000000000000000 : ℝ)^512 ≤ (2500000001215211/2500000000000000 : ℝ)^2097 := by
      have hnat : (25000000049771428921 : ℕ)^512*2500000000000000^2097 ≤ 2500000001215211^2097*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000049771428921 25000000000000000000 2500000001215211 2500000000000000 512 2097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000001215211/2500000000000000 : ℝ)) (X := (25000000049771428921/25000000000000000000 : ℝ)) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100513700033668870769/100000000000000000000 : ℝ) ≤ (250312953428981/250000000000000 : ℝ) ^ (2097/512 : ℝ) := by
    have hpowers : (100513700033668870769/100000000000000000000 : ℝ)^512 ≤ (250312953428981/250000000000000 : ℝ)^2097 := by
      have hnat : (100513700033668870769 : ℕ)^512*250000000000000^2097 ≤ 250312953428981^2097*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100513700033668870769 100000000000000000000 250312953428981 250000000000000 512 2097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250312953428981/250000000000000 : ℝ)) (X := (100513700033668870769/100000000000000000000 : ℝ)) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50513699934126012927/50000000000000000000 : ℝ) ≤ (2506259067364409/2500000000000000 : ℝ) ^ (2097/512 : ℝ) := by
    have hpowers : (50513699934126012927/50000000000000000000 : ℝ)^512 ≤ (2506259067364409/2500000000000000 : ℝ)^2097 := by
      have hnat : (50513699934126012927 : ℕ)^512*2500000000000000^2097 ≤ 2506259067364409^2097*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50513699934126012927 50000000000000000000 2506259067364409 2500000000000000 512 2097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2506259067364409/2500000000000000 : ℝ)) (X := (50513699934126012927/50000000000000000000 : ℝ)) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(49771428921/50000000000000000000 : ℝ) ≤ ((67433531784841725193/67437500000000000000 : ℝ)+2*(3129533074599/674375000000000 : ℝ)*(317/50000 : ℝ))^(2097/512 : ℝ) := by
    rw [show (67433531784841725193/67437500000000000000 : ℝ)+2*(3129533074599/674375000000000 : ℝ)*(317/50000 : ℝ)=(2500000001215211/2500000000000000 : ℝ) by norm_num, show 1+2*(49771428921/50000000000000000000 : ℝ)=(25000000049771428921/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(513699934126012927/100000000000000000000 : ℝ)+(49771428921/50000000000000000000 : ℝ) ≤ ((67433531784841725193/67437500000000000000 : ℝ)+(3129533074599/674375000000000 : ℝ)*((27609/100000 : ℝ)+(317/50000 : ℝ)))^(2097/512 : ℝ) := by
    rw [show (67433531784841725193/67437500000000000000 : ℝ)+(3129533074599/674375000000000 : ℝ)*((27609/100000 : ℝ)+(317/50000 : ℝ))=(250312953428981/250000000000000 : ℝ) by norm_num, show 1+(513699934126012927/100000000000000000000 : ℝ)+(49771428921/50000000000000000000 : ℝ)=(100513700033668870769/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(513699934126012927/100000000000000000000 : ℝ) ≤ ((67433531784841725193/67437500000000000000 : ℝ)+2*(3129533074599/674375000000000 : ℝ)*(27609/100000 : ℝ))^(2097/512 : ℝ) := by
    rw [show (67433531784841725193/67437500000000000000 : ℝ)+2*(3129533074599/674375000000000 : ℝ)*(27609/100000 : ℝ)=(2506259067364409/2500000000000000 : ℝ) by norm_num, show 1+2*(513699934126012927/100000000000000000000 : ℝ)=(50513699934126012927/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (67433531784841725193/67437500000000000000 : ℝ)*(X 1 0+X 2 0)+(3129533074599/674375000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2097/512 : ℝ)) (lo := (317/50000 : ℝ)) (hi := (27609/100000 : ℝ)) (c := (67433531784841725193/67437500000000000000 : ℝ)) (alpha := (3129533074599/674375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (67433531784841725193/67437500000000000000 : ℝ)*(X 0 1+X 2 1)+(3129533074599/674375000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2097/512 : ℝ)) (lo := (317/50000 : ℝ)) (hi := (27609/100000 : ℝ)) (c := (67433531784841725193/67437500000000000000 : ℝ)) (alpha := (3129533074599/674375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (67433531784841725193/67437500000000000000 : ℝ)*(X 0 2+X 1 2)+(3129533074599/674375000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2097/512 : ℝ)) (lo := (317/50000 : ℝ)) (hi := (27609/100000 : ℝ)) (c := (67433531784841725193/67437500000000000000 : ℝ)) (alpha := (3129533074599/674375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-103779709/500000000 : ℝ)*X 0 0+(5687306089/10000000000 : ℝ)*X 0 1+(9791759/19531250 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1354040503/2500000000 : ℝ)*X 1 0+(-2438293649/10000000000 : ℝ)*X 1 1+(5013380959/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5416160981/10000000000 : ℝ)*X 2 0+(5013381627/10000000000 : ℝ)*X 2 1+(-121914707/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4312832117/10000000000 : ℝ)*X 0 0+(5899349/16000000 : ℝ)*X 0 1+(201682659/400000000 : ℝ)*X 0 2+(4312832117/10000000000 : ℝ)*X 1 0+(5899349/16000000 : ℝ)*X 1 1+(201682659/400000000 : ℝ)*X 1 2+(4312832117/10000000000 : ℝ)*X 2 0+(5899349/16000000 : ℝ)*X 2 1+(201682659/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2076326987/10000000000 : ℝ)*X 0 0+(313899573/625000000 : ℝ)*X 0 1+(567811917/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2621459701/5000000000 : ℝ)*X 1 0+(-55423623/312500000 : ℝ)*X 1 1+(709764853/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5242919389/10000000000 : ℝ)*X 2 0+(709764929/1250000000 : ℝ)*X 2 1+(-1773555069/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2157152801/5000000000 : ℝ)*X 0 0+(1004789173/2000000000 : ℝ)*X 0 1+(3705564567/10000000000 : ℝ)*X 0 2+(2157152801/5000000000 : ℝ)*X 1 0+(1004789173/2000000000 : ℝ)*X 1 1+(3705564567/10000000000 : ℝ)*X 1 2+(2157152801/5000000000 : ℝ)*X 2 0+(1004789173/2000000000 : ℝ)*X 2 1+(3705564567/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (703426193235258607250431419/337187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12859253/100000000000000 : ℝ)*(base16) + (127268259/20000000000000 : ℝ)*(base19) + (444569047/100000000000000 : ℝ)*(base23) + (42153381/100000000000000 : ℝ)*(upper2) + (30830503/20000000000000 : ℝ)*(upper3) + (222187870213461/20000000000000 : ℝ)*(major0) + (222187870213461/20000000000000 : ℝ)*(major1) + (222187870213461/20000000000000 : ℝ)*(major2) + (1483849073562423/100000000000000 : ℝ)*(sp0) + (741925782745951/50000000000000 : ℝ)*(sp1) + (1483851770123403/100000000000000 : ℝ)*(sp2) + (738023960148827/100000000000000 : ℝ)*(sp3) + (3141130027/100000000000000 : ℝ)*(sp4) + (2457754751/100000000000000 : ℝ)*(sp7) + (369013208951789/50000000000000 : ℝ)*(f.failure) + (29677044293849/2000000000000 : ℝ)*(f.sum) + (9073203085339/6743750000000000000000000000 : ℝ)*base65 + (3955392454708427027/1348750000000000000000000000000000 : ℝ)*base68 + (1224919936295322973/1348750000000000000000000000000000 : ℝ)*base69 + (4773140270268427027/1348750000000000000000000000000000 : ℝ)*base72 + (6344921402661/6743750000000000000000000000 : ℝ)*base74 + (4491734339049677027/1348750000000000000000000000000000 : ℝ)*base76 + (966308931519677027/1348750000000000000000000000000000 : ℝ)*base78 + (5936662367635927027/1348750000000000000000000000000000 : ℝ)*base80 + (49008919760053/13487500000000000000000000000 : ℝ)*base81 + (16355811/5000000000000000000000 : ℝ)*base89 + (16355811/5000000000000000000000 : ℝ)*base91 + (16355811/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6359907329401326804436883559/674375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6489953/25000000000000 : ℝ)*(base1) + (5803781/250000000000 : ℝ)*(base19) + (297550979/12500000000000 : ℝ)*(base23) + (4535281/2000000000000 : ℝ)*(upper3) + (59678973/25000000000000 : ℝ)*(upper5) + (228353377481621/20000000000000 : ℝ)*(major0) + (228353377481621/20000000000000 : ℝ)*(major1) + (228353377481621/20000000000000 : ℝ)*(major2) + (5333378917/50000000000000 : ℝ)*(sp1) + (12563647551/100000000000000 : ℝ)*(sp2) + (381256880025999/25000000000000 : ℝ)*(sp4) + (30500290117479/2000000000000 : ℝ)*(sp5) + (1906265687611/125000000000 : ℝ)*(sp6) + (379252970175819/50000000000000 : ℝ)*(sp7) + (15170119326229/2000000000000 : ℝ)*(f.failure) + (190628436768023/12500000000000 : ℝ)*(f.sum) + (17090000883129/6743750000000000000000000000 : ℝ)*base65 + (522154919264422147/1348750000000000000000000000000000 : ℝ)*base68 + (6268690243729422147/1348750000000000000000000000000000 : ℝ)*base70 + (3108895280631922147/1348750000000000000000000000000000 : ℝ)*base72 + (16331747650877/3371875000000000000000000000 : ℝ)*base73 + (2869476363028077853/1348750000000000000000000000000000 : ℝ)*base75 + (4212942678153172147/1348750000000000000000000000000000 : ℝ)*base78 + (3884740379271827853/1348750000000000000000000000000000 : ℝ)*base79 + (43722456814033/13487500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (77371/200000000000000000000 : ℝ)*base89 + (77371/200000000000000000000 : ℝ)*base91 + (77371/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1196_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150528399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27609/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (317/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5947/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20197/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1196_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1196_s2_0 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1062986199/5000000000 : ℝ)*x 0 + (2750415993/5000000000 : ℝ)*x 1 + (5167769501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062986199/5000000000 : ℝ)^8389 ≤ (1289359124951/10000000000000 : ℝ)^6341 := by
    have hnat : (1062986199 : ℕ)^8389*10000000000000^6341 ≤ 1289359124951^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062986199 5000000000 1289359124951 10000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2750415993/5000000000 : ℝ)^8389 ≤ (45351598685559/100000000000000 : ℝ)^6341 := by
    have hnat : (2750415993 : ℕ)^8389*100000000000000^6341 ≤ 45351598685559^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750415993 5000000000 45351598685559 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5167769501/10000000000 : ℝ)^8389 ≤ (5219351257303/12500000000000 : ℝ)^6341 := by
    have hnat : (5167769501 : ℕ)^8389*12500000000000^6341 ≤ 5219351257303^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5167769501 10000000000 5219351257303 12500000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1062986199/5000000000 : ℝ), (2750415993/5000000000 : ℝ), (5167769501/10000000000 : ℝ)] ![(1289359124951/10000000000000 : ℝ), (45351598685559/100000000000000 : ℝ), (5219351257303/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1062986199/5000000000 : ℝ)|^8389 ≤ (1289359124951/10000000000000 : ℝ)^6341
        have hw : |(-1062986199/5000000000 : ℝ)|=(1062986199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2750415993/5000000000 : ℝ)|^8389 ≤ (45351598685559/100000000000000 : ℝ)^6341
        have hw : |(2750415993/5000000000 : ℝ)|=(2750415993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5167769501/10000000000 : ℝ)|^8389 ≤ (5219351257303/12500000000000 : ℝ)^6341
        have hw : |(5167769501/10000000000 : ℝ)|=(5167769501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s2_1 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1342894511/2500000000 : ℝ)*x 0 + (-1149388227/5000000000 : ℝ)*x 1 + (161492931/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342894511/2500000000 : ℝ)^8389 ≤ (43947167310809/100000000000000 : ℝ)^6341 := by
    have hnat : (1342894511 : ℕ)^8389*100000000000000^6341 ≤ 43947167310809^6341*2500000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342894511 2500000000 43947167310809 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1149388227/5000000000 : ℝ)^8389 ≤ (7148988373321/50000000000000 : ℝ)^6341 := by
    have hnat : (1149388227 : ℕ)^8389*50000000000000^6341 ≤ 7148988373321^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1149388227 5000000000 7148988373321 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (161492931/312500000 : ℝ)^8389 ≤ (10438713981727/25000000000000 : ℝ)^6341 := by
    have hnat : (161492931 : ℕ)^8389*25000000000000^6341 ≤ 10438713981727^6341*312500000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161492931 312500000 10438713981727 25000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342894511/2500000000 : ℝ), (-1149388227/5000000000 : ℝ), (161492931/312500000 : ℝ)] ![(43947167310809/100000000000000 : ℝ), (7148988373321/50000000000000 : ℝ), (10438713981727/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342894511/2500000000 : ℝ)|^8389 ≤ (43947167310809/100000000000000 : ℝ)^6341
        have hw : |(1342894511/2500000000 : ℝ)|=(1342894511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1149388227/5000000000 : ℝ)|^8389 ≤ (7148988373321/50000000000000 : ℝ)^6341
        have hw : |(-1149388227/5000000000 : ℝ)|=(1149388227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(161492931/312500000 : ℝ)|^8389 ≤ (10438713981727/25000000000000 : ℝ)^6341
        have hw : |(161492931/312500000 : ℝ)|=(161492931/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s2_2 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5371579851/10000000000 : ℝ)*x 0 + (1291942817/2500000000 : ℝ)*x 1 + (-574694339/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5371579851/10000000000 : ℝ)^8389 ≤ (10986796717373/25000000000000 : ℝ)^6341 := by
    have hnat : (5371579851 : ℕ)^8389*25000000000000^6341 ≤ 10986796717373^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371579851 10000000000 10986796717373 25000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1291942817/2500000000 : ℝ)^8389 ≤ (41754828946703/100000000000000 : ℝ)^6341 := by
    have hnat : (1291942817 : ℕ)^8389*100000000000000^6341 ≤ 41754828946703^6341*2500000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1291942817 2500000000 41754828946703 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (574694339/2500000000 : ℝ)^8389 ≤ (7148992084457/50000000000000 : ℝ)^6341 := by
    have hnat : (574694339 : ℕ)^8389*50000000000000^6341 ≤ 7148992084457^6341*2500000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      574694339 2500000000 7148992084457 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5371579851/10000000000 : ℝ), (1291942817/2500000000 : ℝ), (-574694339/2500000000 : ℝ)] ![(10986796717373/25000000000000 : ℝ), (41754828946703/100000000000000 : ℝ), (7148992084457/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5371579851/10000000000 : ℝ)|^8389 ≤ (10986796717373/25000000000000 : ℝ)^6341
        have hw : |(5371579851/10000000000 : ℝ)|=(5371579851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1291942817/2500000000 : ℝ)|^8389 ≤ (41754828946703/100000000000000 : ℝ)^6341
        have hw : |(1291942817/2500000000 : ℝ)|=(1291942817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-574694339/2500000000 : ℝ)|^8389 ≤ (7148992084457/50000000000000 : ℝ)^6341
        have hw : |(-574694339/2500000000 : ℝ)|=(574694339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s2_3 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (543440691/1250000000 : ℝ)*x 0 + (503165597/1250000000 : ℝ)*x 1 + (2347482747/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543440691/1250000000 : ℝ)^8389 ≤ (16610110240039/50000000000000 : ℝ)^6341 := by
    have hnat : (543440691 : ℕ)^8389*50000000000000^6341 ≤ 16610110240039^6341*1250000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543440691 1250000000 16610110240039 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (503165597/1250000000 : ℝ)^8389 ≤ (15001356857359/50000000000000 : ℝ)^6341 := by
    have hnat : (503165597 : ℕ)^8389*50000000000000^6341 ≤ 15001356857359^6341*1250000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503165597 1250000000 15001356857359 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2347482747/5000000000 : ℝ)^8389 ≤ (18388532896081/50000000000000 : ℝ)^6341 := by
    have hnat : (2347482747 : ℕ)^8389*50000000000000^6341 ≤ 18388532896081^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2347482747 5000000000 18388532896081 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543440691/1250000000 : ℝ), (503165597/1250000000 : ℝ), (2347482747/5000000000 : ℝ)] ![(16610110240039/50000000000000 : ℝ), (15001356857359/50000000000000 : ℝ), (18388532896081/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543440691/1250000000 : ℝ)|^8389 ≤ (16610110240039/50000000000000 : ℝ)^6341
        have hw : |(543440691/1250000000 : ℝ)|=(543440691/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(503165597/1250000000 : ℝ)|^8389 ≤ (15001356857359/50000000000000 : ℝ)^6341
        have hw : |(503165597/1250000000 : ℝ)|=(503165597/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2347482747/5000000000 : ℝ)|^8389 ≤ (18388532896081/50000000000000 : ℝ)^6341
        have hw : |(2347482747/5000000000 : ℝ)|=(2347482747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s2_4 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1063029991/5000000000 : ℝ)*x 0 + (5169982021/10000000000 : ℝ)*x 1 + (219943957/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1063029991/5000000000 : ℝ)^8389 ≤ (6447146996137/50000000000000 : ℝ)^6341 := by
    have hnat : (1063029991 : ℕ)^8389*50000000000000^6341 ≤ 6447146996137^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063029991 5000000000 6447146996137 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5169982021/10000000000 : ℝ)^8389 ≤ (41778462340367/100000000000000 : ℝ)^6341 := by
    have hnat : (5169982021 : ℕ)^8389*100000000000000^6341 ≤ 41778462340367^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5169982021 10000000000 41778462340367 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219943957/400000000 : ℝ)^8389 ≤ (22663621824823/50000000000000 : ℝ)^6341 := by
    have hnat : (219943957 : ℕ)^8389*50000000000000^6341 ≤ 22663621824823^6341*400000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219943957 400000000 22663621824823 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1063029991/5000000000 : ℝ), (5169982021/10000000000 : ℝ), (219943957/400000000 : ℝ)] ![(6447146996137/50000000000000 : ℝ), (41778462340367/100000000000000 : ℝ), (22663621824823/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1063029991/5000000000 : ℝ)|^8389 ≤ (6447146996137/50000000000000 : ℝ)^6341
        have hw : |(-1063029991/5000000000 : ℝ)|=(1063029991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5169982021/10000000000 : ℝ)|^8389 ≤ (41778462340367/100000000000000 : ℝ)^6341
        have hw : |(5169982021/10000000000 : ℝ)|=(5169982021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(219943957/400000000 : ℝ)|^8389 ≤ (22663621824823/50000000000000 : ℝ)^6341
        have hw : |(219943957/400000000 : ℝ)|=(219943957/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s2_5 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5286772257/10000000000 : ℝ)*x 0 + (-1967949679/10000000000 : ℝ)*x 1 + (2749299471/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286772257/10000000000 : ℝ)^8389 ≤ (21515795792091/50000000000000 : ℝ)^6341 := by
    have hnat : (5286772257 : ℕ)^8389*50000000000000^6341 ≤ 21515795792091^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286772257 10000000000 21515795792091 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1967949679/10000000000 : ℝ)^8389 ≤ (1455145571313/12500000000000 : ℝ)^6341 := by
    have hnat : (1967949679 : ℕ)^8389*12500000000000^6341 ≤ 1455145571313^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1967949679 10000000000 1455145571313 12500000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2749299471/5000000000 : ℝ)^8389 ≤ (22663621917523/50000000000000 : ℝ)^6341 := by
    have hnat : (2749299471 : ℕ)^8389*50000000000000^6341 ≤ 22663621917523^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2749299471 5000000000 22663621917523 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286772257/10000000000 : ℝ), (-1967949679/10000000000 : ℝ), (2749299471/5000000000 : ℝ)] ![(21515795792091/50000000000000 : ℝ), (1455145571313/12500000000000 : ℝ), (22663621917523/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286772257/10000000000 : ℝ)|^8389 ≤ (21515795792091/50000000000000 : ℝ)^6341
        have hw : |(5286772257/10000000000 : ℝ)|=(5286772257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1967949679/10000000000 : ℝ)|^8389 ≤ (1455145571313/12500000000000 : ℝ)^6341
        have hw : |(-1967949679/10000000000 : ℝ)|=(1967949679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2749299471/5000000000 : ℝ)|^8389 ≤ (22663621917523/50000000000000 : ℝ)^6341
        have hw : |(2749299471/5000000000 : ℝ)|=(2749299471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s2_6 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (211470897/400000000 : ℝ)*x 0 + (5498598957/10000000000 : ℝ)*x 1 + (-983974713/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211470897/400000000 : ℝ)^8389 ≤ (21515796696633/50000000000000 : ℝ)^6341 := by
    have hnat : (211470897 : ℕ)^8389*50000000000000^6341 ≤ 21515796696633^6341*400000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211470897 400000000 21515796696633 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5498598957/10000000000 : ℝ)^8389 ≤ (22663621999317/50000000000000 : ℝ)^6341 := by
    have hnat : (5498598957 : ℕ)^8389*50000000000000^6341 ≤ 22663621999317^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5498598957 10000000000 22663621999317 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (983974713/5000000000 : ℝ)^8389 ≤ (2910290647637/25000000000000 : ℝ)^6341 := by
    have hnat : (983974713 : ℕ)^8389*25000000000000^6341 ≤ 2910290647637^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      983974713 5000000000 2910290647637 25000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211470897/400000000 : ℝ), (5498598957/10000000000 : ℝ), (-983974713/5000000000 : ℝ)] ![(21515796696633/50000000000000 : ℝ), (22663621999317/50000000000000 : ℝ), (2910290647637/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211470897/400000000 : ℝ)|^8389 ≤ (21515796696633/50000000000000 : ℝ)^6341
        have hw : |(211470897/400000000 : ℝ)|=(211470897/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5498598957/10000000000 : ℝ)|^8389 ≤ (22663621999317/50000000000000 : ℝ)^6341
        have hw : |(5498598957/10000000000 : ℝ)|=(5498598957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-983974713/5000000000 : ℝ)|^8389 ≤ (2910290647637/25000000000000 : ℝ)^6341
        have hw : |(-983974713/5000000000 : ℝ)|=(983974713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s2_7 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (869540781/2000000000 : ℝ)*x 0 + (4690519793/10000000000 : ℝ)*x 1 + (32238501/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (869540781/2000000000 : ℝ)^8389 ≤ (16611011862139/50000000000000 : ℝ)^6341 := by
    have hnat : (869540781 : ℕ)^8389*50000000000000^6341 ≤ 16611011862139^6341*2000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869540781 2000000000 16611011862139 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4690519793/10000000000 : ℝ)^8389 ≤ (36731000807149/100000000000000 : ℝ)^6341 := by
    have hnat : (4690519793 : ℕ)^8389*100000000000000^6341 ≤ 36731000807149^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4690519793 10000000000 36731000807149 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32238501/80000000 : ℝ)^8389 ≤ (30046975451833/100000000000000 : ℝ)^6341 := by
    have hnat : (32238501 : ℕ)^8389*100000000000000^6341 ≤ 30046975451833^6341*80000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32238501 80000000 30046975451833 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(869540781/2000000000 : ℝ), (4690519793/10000000000 : ℝ), (32238501/80000000 : ℝ)] ![(16611011862139/50000000000000 : ℝ), (36731000807149/100000000000000 : ℝ), (30046975451833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(869540781/2000000000 : ℝ)|^8389 ≤ (16611011862139/50000000000000 : ℝ)^6341
        have hw : |(869540781/2000000000 : ℝ)|=(869540781/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4690519793/10000000000 : ℝ)|^8389 ≤ (36731000807149/100000000000000 : ℝ)^6341
        have hw : |(4690519793/10000000000 : ℝ)|=(4690519793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(32238501/80000000 : ℝ)|^8389 ≤ (30046975451833/100000000000000 : ℝ)^6341
        have hw : |(32238501/80000000 : ℝ)|=(32238501/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1196_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150528399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20197/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5947/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2327/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16347/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20197/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5947/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20197/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5947/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20197/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5947/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20197/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5947/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20197/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5947/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20197/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5947/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5947/100000 : ℝ) ^ (2097/512 : ℝ) ≤ (119343356858487/12500000000000000000 : ℝ) := by
    have hpowers : (5947/100000 : ℝ)^2097 ≤ (119343356858487/12500000000000000000 : ℝ)^512 := by
      have hnat : (5947 : ℕ)^2097*12500000000000000000^512 ≤ 119343356858487^512*100000^2097 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5947 100000 119343356858487 12500000000000000000 2097 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5947/100000 : ℝ)) (X := (119343356858487/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have hpowhi : (20197/100000 : ℝ) ^ (2097/512 : ℝ) ≤ (35694495872424303/25000000000000000000 : ℝ) := by
    have hpowers : (20197/100000 : ℝ)^2097 ≤ (35694495872424303/25000000000000000000 : ℝ)^512 := by
      have hnat : (20197 : ℕ)^2097*25000000000000000000^512 ≤ 35694495872424303^512*100000^2097 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20197 100000 35694495872424303 25000000000000000000 2097 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20197/100000 : ℝ)) (X := (35694495872424303/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250119343356858487/6250000000000000000 : ℝ) ≤ (2000009324308291/2000000000000000 : ℝ) ^ (2097/512 : ℝ) := by
    have hpowers : (6250119343356858487/6250000000000000000 : ℝ)^512 ≤ (2000009324308291/2000000000000000 : ℝ)^2097 := by
      have hnat : (6250119343356858487 : ℕ)^512*2000000000000000^2097 ≤ 2000009324308291^2097*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250119343356858487 6250000000000000000 2000009324308291 2000000000000000 512 2097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000009324308291/2000000000000000 : ℝ)) (X := (6250119343356858487/6250000000000000000 : ℝ)) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25035933182586141277/25000000000000000000 : ℝ) ≤ (10003507449552359/10000000000000000 : ℝ) ^ (2097/512 : ℝ) := by
    have hpowers : (25035933182586141277/25000000000000000000 : ℝ)^512 ≤ (10003507449552359/10000000000000000 : ℝ)^2097 := by
      have hnat : (25035933182586141277 : ℕ)^512*10000000000000000^2097 ≤ 10003507449552359^2097*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25035933182586141277 25000000000000000000 10003507449552359 10000000000000000 512 2097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003507449552359/10000000000000000 : ℝ)) (X := (25035933182586141277/25000000000000000000 : ℝ)) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12535694495872424303/12500000000000000000 : ℝ) ≤ (10006968277563263/10000000000000000 : ℝ) ^ (2097/512 : ℝ) := by
    have hpowers : (12535694495872424303/12500000000000000000 : ℝ)^512 ≤ (10006968277563263/10000000000000000 : ℝ)^2097 := by
      have hnat : (12535694495872424303 : ℕ)^512*10000000000000000^2097 ≤ 10006968277563263^2097*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12535694495872424303 12500000000000000000 10006968277563263 10000000000000000 512 2097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006968277563263/10000000000000000 : ℝ)) (X := (12535694495872424303/12500000000000000000 : ℝ)) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(119343356858487/12500000000000000000 : ℝ) ≤ ((1249644747970210891/1250000000000000000 : ℝ)+2*(144201167121/59375000000000 : ℝ)*(5947/100000 : ℝ))^(2097/512 : ℝ) := by
    rw [show (1249644747970210891/1250000000000000000 : ℝ)+2*(144201167121/59375000000000 : ℝ)*(5947/100000 : ℝ)=(2000009324308291/2000000000000000 : ℝ) by norm_num, show 1+2*(119343356858487/12500000000000000000 : ℝ)=(6250119343356858487/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35694495872424303/25000000000000000000 : ℝ)+(119343356858487/12500000000000000000 : ℝ) ≤ ((1249644747970210891/1250000000000000000 : ℝ)+(144201167121/59375000000000 : ℝ)*((20197/100000 : ℝ)+(5947/100000 : ℝ)))^(2097/512 : ℝ) := by
    rw [show (1249644747970210891/1250000000000000000 : ℝ)+(144201167121/59375000000000 : ℝ)*((20197/100000 : ℝ)+(5947/100000 : ℝ))=(10003507449552359/10000000000000000 : ℝ) by norm_num, show 1+(35694495872424303/25000000000000000000 : ℝ)+(119343356858487/12500000000000000000 : ℝ)=(25035933182586141277/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35694495872424303/25000000000000000000 : ℝ) ≤ ((1249644747970210891/1250000000000000000 : ℝ)+2*(144201167121/59375000000000 : ℝ)*(20197/100000 : ℝ))^(2097/512 : ℝ) := by
    rw [show (1249644747970210891/1250000000000000000 : ℝ)+2*(144201167121/59375000000000 : ℝ)*(20197/100000 : ℝ)=(10006968277563263/10000000000000000 : ℝ) by norm_num, show 1+2*(35694495872424303/25000000000000000000 : ℝ)=(12535694495872424303/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1249644747970210891/1250000000000000000 : ℝ)*(X 1 0+X 2 0)+(144201167121/59375000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2097/512 : ℝ)) (lo := (5947/100000 : ℝ)) (hi := (20197/100000 : ℝ)) (c := (1249644747970210891/1250000000000000000 : ℝ)) (alpha := (144201167121/59375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1249644747970210891/1250000000000000000 : ℝ)*(X 0 1+X 2 1)+(144201167121/59375000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2097/512 : ℝ)) (lo := (5947/100000 : ℝ)) (hi := (20197/100000 : ℝ)) (c := (1249644747970210891/1250000000000000000 : ℝ)) (alpha := (144201167121/59375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1249644747970210891/1250000000000000000 : ℝ)*(X 0 2+X 1 2)+(144201167121/59375000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2097/512 : ℝ)) (lo := (5947/100000 : ℝ)) (hi := (20197/100000 : ℝ)) (c := (1249644747970210891/1250000000000000000 : ℝ)) (alpha := (144201167121/59375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1062986199/5000000000 : ℝ)*X 0 0+(2750415993/5000000000 : ℝ)*X 0 1+(5167769501/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1342894511/2500000000 : ℝ)*X 1 0+(-1149388227/5000000000 : ℝ)*X 1 1+(161492931/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5371579851/10000000000 : ℝ)*X 2 0+(1291942817/2500000000 : ℝ)*X 2 1+(-574694339/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((543440691/1250000000 : ℝ)*X 0 0+(503165597/1250000000 : ℝ)*X 0 1+(2347482747/5000000000 : ℝ)*X 0 2+(543440691/1250000000 : ℝ)*X 1 0+(503165597/1250000000 : ℝ)*X 1 1+(2347482747/5000000000 : ℝ)*X 1 2+(543440691/1250000000 : ℝ)*X 2 0+(503165597/1250000000 : ℝ)*X 2 1+(2347482747/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1063029991/5000000000 : ℝ)*X 0 0+(5169982021/10000000000 : ℝ)*X 0 1+(219943957/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5286772257/10000000000 : ℝ)*X 1 0+(-1967949679/10000000000 : ℝ)*X 1 1+(2749299471/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((211470897/400000000 : ℝ)*X 2 0+(5498598957/10000000000 : ℝ)*X 2 1+(-983974713/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((869540781/2000000000 : ℝ)*X 0 0+(4690519793/10000000000 : ℝ)*X 0 1+(32238501/80000000 : ℝ)*X 0 2+(869540781/2000000000 : ℝ)*X 1 0+(4690519793/10000000000 : ℝ)*X 1 1+(32238501/80000000 : ℝ)*X 1 2+(869540781/2000000000 : ℝ)*X 2 0+(4690519793/10000000000 : ℝ)*X 2 1+(32238501/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2909412706955217646389346713/1187500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1164797/4000000000000 : ℝ)*(base19) + (502036461/50000000000000 : ℝ)*(base23) + (183372143/100000000000000 : ℝ)*(upper2) + (206514303/50000000000000 : ℝ)*(upper3) + (101109763/50000000000000 : ℝ)*(upper4) + (2247927232902499/100000000000000 : ℝ)*(major0) + (2247927232902499/100000000000000 : ℝ)*(major1) + (2247927232902499/100000000000000 : ℝ)*(major2) + (300246993545277/10000000000000 : ℝ)*(sp0) + (1501248395353253/50000000000000 : ℝ)*(sp1) + (3002495815753509/100000000000000 : ℝ)*(sp2) + (93334063443113/6250000000000 : ℝ)*(sp3) + (26884373661/100000000000000 : ℝ)*(sp4) + (1254922103/10000000000000 : ℝ)*(sp7) + (746678782155419/50000000000000 : ℝ)*(f.failure) + (3002496819826431/100000000000000 : ℝ)*(f.sum) + (479583757751/742187500000000000000000000 : ℝ)*base65 + (8021865975625984429/2375000000000000000000000000000000 : ℝ)*base68 + (3034345070875984429/2375000000000000000000000000000000 : ℝ)*base70 + (5786348069249015571/2375000000000000000000000000000000 : ℝ)*base71 + (20179067868617/5937500000000000000000000000 : ℝ)*base74 + (16728140393750984429/2375000000000000000000000000000000 : ℝ)*base76 + (14219039943624015571/2375000000000000000000000000000000 : ℝ)*base77 + (7442673089250984429/2375000000000000000000000000000000 : ℝ)*base80 + (20042069698617/5937500000000000000000000000 : ℝ)*base82 + (41244181/5000000000000000000000 : ℝ)*base89 + (41244181/5000000000000000000000 : ℝ)*base91 + (41244181/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1599503336116028684236916643/296875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (43281061/3125000000000 : ℝ)*(base19) + (1592769549/100000000000000 : ℝ)*(base23) + (24601213/100000000000000 : ℝ)*(upper2) + (90881473/50000000000000 : ℝ)*(upper3) + (112595201/100000000000000 : ℝ)*(upper5) + (1139146716548111/50000000000000 : ℝ)*(major0) + (1139146716548111/50000000000000 : ℝ)*(major1) + (1139146716548111/50000000000000 : ℝ)*(major2) + (540287307/4000000000000 : ℝ)*(sp1) + (1753035441/10000000000000 : ℝ)*(sp2) + (152152802584731/5000000000000 : ℝ)*(sp4) + (380380144939749/12500000000000 : ℝ)*(sp5) + (3043036928570661/100000000000000 : ℝ)*(sp6) + (756765317452231/50000000000000 : ℝ)*(sp7) + (756765317452231/50000000000000 : ℝ)*(f.failure) + (152152802584731/5000000000000 : ℝ)*(f.sum) + (413467018099/5937500000000000000000000000 : ℝ)*base65 + (240142272633261119/1187500000000000000000000000000000 : ℝ)*base67 + (5688543246633261119/1187500000000000000000000000000000 : ℝ)*base69 + (2687204085633261119/1187500000000000000000000000000000 : ℝ)*base71 + (4705784839987/2968750000000000000000000000 : ℝ)*base73 + (13167020951883261119/1187500000000000000000000000000000 : ℝ)*base75 + (2736271358820761119/1187500000000000000000000000000000 : ℝ)*base77 + (6823185433804238881/1187500000000000000000000000000000 : ℝ)*base80 + (8858636048737/2968750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (8591831/5000000000000000000000 : ℝ)*base90 + (8591831/5000000000000000000000 : ℝ)*base92 + (8591831/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1196_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150528399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20197/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5947/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2327/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16347/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1196_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1196_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150528399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2327/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16347/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1196_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1196_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1196_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150528399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2327/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16347/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1196_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

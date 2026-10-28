-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1267_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:19:54.654889+00:00
-- url     : https://prove2.me/submissions/838ad036-0c22-425b-a86d-fb902aaedf8f

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
theorem support_rectangle_w1267_s3_0 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2105860443/10000000000 : ℝ)*x 0 + (135437899/250000000 : ℝ)*x 1 + (5242489559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2105860443/10000000000 : ℝ)^2115 ≤ (6401802052969/50000000000000 : ℝ)^1603 := by
    have hnat : (2105860443 : ℕ)^2115*50000000000000^1603 ≤ 6401802052969^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105860443 10000000000 6401802052969 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135437899/250000000 : ℝ)^2115 ≤ (44542612361741/100000000000000 : ℝ)^1603 := by
    have hnat : (135437899 : ℕ)^2115*100000000000000^1603 ≤ 44542612361741^1603*250000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135437899 250000000 44542612361741 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242489559/10000000000 : ℝ)^2115 ≤ (42653783520947/100000000000000 : ℝ)^1603 := by
    have hnat : (5242489559 : ℕ)^2115*100000000000000^1603 ≤ 42653783520947^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242489559 10000000000 42653783520947 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2105860443/10000000000 : ℝ), (135437899/250000000 : ℝ), (5242489559/10000000000 : ℝ)] ![(6401802052969/50000000000000 : ℝ), (44542612361741/100000000000000 : ℝ), (42653783520947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2105860443/10000000000 : ℝ)|^2115 ≤ (6401802052969/50000000000000 : ℝ)^1603
        have hw : |(-2105860443/10000000000 : ℝ)|=(2105860443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(135437899/250000000 : ℝ)|^2115 ≤ (44542612361741/100000000000000 : ℝ)^1603
        have hw : |(135437899/250000000 : ℝ)|=(135437899/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242489559/10000000000 : ℝ)|^2115 ≤ (42653783520947/100000000000000 : ℝ)^1603
        have hw : |(5242489559/10000000000 : ℝ)|=(5242489559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s3_1 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2675472593/5000000000 : ℝ)*x 0 + (-274388549/1250000000 : ℝ)*x 1 + (65531121/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675472593/5000000000 : ℝ)^2115 ≤ (43821869340011/100000000000000 : ℝ)^1603 := by
    have hnat : (2675472593 : ℕ)^2115*100000000000000^1603 ≤ 43821869340011^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675472593 5000000000 43821869340011 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (274388549/1250000000 : ℝ)^2115 ≤ (13524345827103/100000000000000 : ℝ)^1603 := by
    have hnat : (274388549 : ℕ)^2115*100000000000000^1603 ≤ 13524345827103^1603*1250000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274388549 1250000000 13524345827103 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65531121/125000000 : ℝ)^2115 ≤ (21326892409933/50000000000000 : ℝ)^1603 := by
    have hnat : (65531121 : ℕ)^2115*50000000000000^1603 ≤ 21326892409933^1603*125000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65531121 125000000 21326892409933 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675472593/5000000000 : ℝ), (-274388549/1250000000 : ℝ), (65531121/125000000 : ℝ)] ![(43821869340011/100000000000000 : ℝ), (13524345827103/100000000000000 : ℝ), (21326892409933/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675472593/5000000000 : ℝ)|^2115 ≤ (43821869340011/100000000000000 : ℝ)^1603
        have hw : |(2675472593/5000000000 : ℝ)|=(2675472593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-274388549/1250000000 : ℝ)|^2115 ≤ (13524345827103/100000000000000 : ℝ)^1603
        have hw : |(-274388549/1250000000 : ℝ)|=(274388549/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65531121/125000000 : ℝ)|^2115 ≤ (21326892409933/50000000000000 : ℝ)^1603
        have hw : |(65531121/125000000 : ℝ)|=(65531121/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s3_2 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5350945173/10000000000 : ℝ)*x 0 + (1310622539/2500000000 : ℝ)*x 1 + (-2195107781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350945173/10000000000 : ℝ)^2115 ≤ (21910934599771/50000000000000 : ℝ)^1603 := by
    have hnat : (5350945173 : ℕ)^2115*50000000000000^1603 ≤ 21910934599771^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350945173 10000000000 21910934599771 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310622539/2500000000 : ℝ)^2115 ≤ (8530757985933/20000000000000 : ℝ)^1603 := by
    have hnat : (1310622539 : ℕ)^2115*20000000000000^1603 ≤ 8530757985933^1603*2500000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310622539 2500000000 8530757985933 20000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2195107781/10000000000 : ℝ)^2115 ≤ (3381085215071/25000000000000 : ℝ)^1603 := by
    have hnat : (2195107781 : ℕ)^2115*25000000000000^1603 ≤ 3381085215071^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195107781 10000000000 3381085215071 25000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350945173/10000000000 : ℝ), (1310622539/2500000000 : ℝ), (-2195107781/10000000000 : ℝ)] ![(21910934599771/50000000000000 : ℝ), (8530757985933/20000000000000 : ℝ), (3381085215071/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350945173/10000000000 : ℝ)|^2115 ≤ (21910934599771/50000000000000 : ℝ)^1603
        have hw : |(5350945173/10000000000 : ℝ)|=(5350945173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310622539/2500000000 : ℝ)|^2115 ≤ (8530757985933/20000000000000 : ℝ)^1603
        have hw : |(1310622539/2500000000 : ℝ)|=(1310622539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2195107781/10000000000 : ℝ)|^2115 ≤ (3381085215071/25000000000000 : ℝ)^1603
        have hw : |(-2195107781/10000000000 : ℝ)|=(2195107781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s3_3 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (217288691/500000000 : ℝ)*x 0 + (834185287/2000000000 : ℝ)*x 1 + (2263846343/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217288691/500000000 : ℝ)^2115 ≤ (33301619229771/100000000000000 : ℝ)^1603 := by
    have hnat : (217288691 : ℕ)^2115*100000000000000^1603 ≤ 33301619229771^1603*500000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217288691 500000000 33301619229771 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (834185287/2000000000 : ℝ)^2115 ≤ (15772639529661/50000000000000 : ℝ)^1603 := by
    have hnat : (834185287 : ℕ)^2115*50000000000000^1603 ≤ 15772639529661^1603*2000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834185287 2000000000 15772639529661 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2263846343/5000000000 : ℝ)^2115 ≤ (35153101693689/100000000000000 : ℝ)^1603 := by
    have hnat : (2263846343 : ℕ)^2115*100000000000000^1603 ≤ 35153101693689^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2263846343 5000000000 35153101693689 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(217288691/500000000 : ℝ), (834185287/2000000000 : ℝ), (2263846343/5000000000 : ℝ)] ![(33301619229771/100000000000000 : ℝ), (15772639529661/50000000000000 : ℝ), (35153101693689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(217288691/500000000 : ℝ)|^2115 ≤ (33301619229771/100000000000000 : ℝ)^1603
        have hw : |(217288691/500000000 : ℝ)|=(217288691/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(834185287/2000000000 : ℝ)|^2115 ≤ (15772639529661/50000000000000 : ℝ)^1603
        have hw : |(834185287/2000000000 : ℝ)|=(834185287/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2263846343/5000000000 : ℝ)|^2115 ≤ (35153101693689/100000000000000 : ℝ)^1603
        have hw : |(2263846343/5000000000 : ℝ)|=(2263846343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s3_4 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-210587431/1000000000 : ℝ)*x 0 + (5243116037/10000000000 : ℝ)*x 1 + (5416885741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210587431/1000000000 : ℝ)^2115 ≤ (160046441829/1250000000000 : ℝ)^1603 := by
    have hnat : (210587431 : ℕ)^2115*1250000000000^1603 ≤ 160046441829^1603*1000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210587431 1000000000 160046441829 1250000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243116037/10000000000 : ℝ)^2115 ≤ (4266050880989/10000000000000 : ℝ)^1603 := by
    have hnat : (5243116037 : ℕ)^2115*10000000000000^1603 ≤ 4266050880989^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243116037 10000000000 4266050880989 10000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416885741/10000000000 : ℝ)^2115 ≤ (5566971978901/12500000000000 : ℝ)^1603 := by
    have hnat : (5416885741 : ℕ)^2115*12500000000000^1603 ≤ 5566971978901^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416885741 10000000000 5566971978901 12500000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-210587431/1000000000 : ℝ), (5243116037/10000000000 : ℝ), (5416885741/10000000000 : ℝ)] ![(160046441829/1250000000000 : ℝ), (4266050880989/10000000000000 : ℝ), (5566971978901/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-210587431/1000000000 : ℝ)|^2115 ≤ (160046441829/1250000000000 : ℝ)^1603
        have hw : |(-210587431/1000000000 : ℝ)|=(210587431/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243116037/10000000000 : ℝ)|^2115 ≤ (4266050880989/10000000000000 : ℝ)^1603
        have hw : |(5243116037/10000000000 : ℝ)|=(5243116037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416885741/10000000000 : ℝ)|^2115 ≤ (5566971978901/12500000000000 : ℝ)^1603
        have hw : |(5416885741/10000000000 : ℝ)|=(5416885741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s3_5 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5306218407/10000000000 : ℝ)*x 0 + (-2020711597/10000000000 : ℝ)*x 1 + (5416885577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5306218407/10000000000 : ℝ)^2115 ≤ (43339228969629/100000000000000 : ℝ)^1603 := by
    have hnat : (5306218407 : ℕ)^2115*100000000000000^1603 ≤ 43339228969629^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5306218407 10000000000 43339228969629 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2020711597/10000000000 : ℝ)^2115 ≤ (6062498479117/50000000000000 : ℝ)^1603 := by
    have hnat : (2020711597 : ℕ)^2115*50000000000000^1603 ≤ 6062498479117^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2020711597 10000000000 6062498479117 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416885577/10000000000 : ℝ)^2115 ≤ (44535774052191/100000000000000 : ℝ)^1603 := by
    have hnat : (5416885577 : ℕ)^2115*100000000000000^1603 ≤ 44535774052191^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416885577 10000000000 44535774052191 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5306218407/10000000000 : ℝ), (-2020711597/10000000000 : ℝ), (5416885577/10000000000 : ℝ)] ![(43339228969629/100000000000000 : ℝ), (6062498479117/50000000000000 : ℝ), (44535774052191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5306218407/10000000000 : ℝ)|^2115 ≤ (43339228969629/100000000000000 : ℝ)^1603
        have hw : |(5306218407/10000000000 : ℝ)|=(5306218407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2020711597/10000000000 : ℝ)|^2115 ≤ (6062498479117/50000000000000 : ℝ)^1603
        have hw : |(-2020711597/10000000000 : ℝ)|=(2020711597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416885577/10000000000 : ℝ)|^2115 ≤ (44535774052191/100000000000000 : ℝ)^1603
        have hw : |(5416885577/10000000000 : ℝ)|=(5416885577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s3_6 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2653108861/5000000000 : ℝ)*x 0 + (270844301/500000000 : ℝ)*x 1 + (-505177981/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2653108861/5000000000 : ℝ)^2115 ≤ (1354350674619/3125000000000 : ℝ)^1603 := by
    have hnat : (2653108861 : ℕ)^2115*3125000000000^1603 ≤ 1354350674619^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2653108861 5000000000 1354350674619 3125000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270844301/500000000 : ℝ)^2115 ≤ (22267889428853/50000000000000 : ℝ)^1603 := by
    have hnat : (270844301 : ℕ)^2115*50000000000000^1603 ≤ 22267889428853^1603*500000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270844301 500000000 22267889428853 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (505177981/2500000000 : ℝ)^2115 ≤ (6062499773527/50000000000000 : ℝ)^1603 := by
    have hnat : (505177981 : ℕ)^2115*50000000000000^1603 ≤ 6062499773527^1603*2500000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505177981 2500000000 6062499773527 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2653108861/5000000000 : ℝ), (270844301/500000000 : ℝ), (-505177981/2500000000 : ℝ)] ![(1354350674619/3125000000000 : ℝ), (22267889428853/50000000000000 : ℝ), (6062499773527/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2653108861/5000000000 : ℝ)|^2115 ≤ (1354350674619/3125000000000 : ℝ)^1603
        have hw : |(2653108861/5000000000 : ℝ)|=(2653108861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270844301/500000000 : ℝ)|^2115 ≤ (22267889428853/50000000000000 : ℝ)^1603
        have hw : |(270844301/500000000 : ℝ)|=(270844301/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-505177981/2500000000 : ℝ)|^2115 ≤ (6062499773527/50000000000000 : ℝ)^1603
        have hw : |(-505177981/2500000000 : ℝ)|=(505177981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s3_7 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2172900693/5000000000 : ℝ)*x 0 + (1131603727/2500000000 : ℝ)*x 1 + (4172210101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2172900693/5000000000 : ℝ)^2115 ≤ (33301897937667/100000000000000 : ℝ)^1603 := by
    have hnat : (2172900693 : ℕ)^2115*100000000000000^1603 ≤ 33301897937667^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172900693 5000000000 33301897937667 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1131603727/2500000000 : ℝ)^2115 ≤ (35140012907019/100000000000000 : ℝ)^1603 := by
    have hnat : (1131603727 : ℕ)^2115*100000000000000^1603 ≤ 35140012907019^1603*2500000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131603727 2500000000 35140012907019 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172210101/10000000000 : ℝ)^2115 ≤ (31558089146197/100000000000000 : ℝ)^1603 := by
    have hnat : (4172210101 : ℕ)^2115*100000000000000^1603 ≤ 31558089146197^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172210101 10000000000 31558089146197 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2172900693/5000000000 : ℝ), (1131603727/2500000000 : ℝ), (4172210101/10000000000 : ℝ)] ![(33301897937667/100000000000000 : ℝ), (35140012907019/100000000000000 : ℝ), (31558089146197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2172900693/5000000000 : ℝ)|^2115 ≤ (33301897937667/100000000000000 : ℝ)^1603
        have hw : |(2172900693/5000000000 : ℝ)|=(2172900693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1131603727/2500000000 : ℝ)|^2115 ≤ (35140012907019/100000000000000 : ℝ)^1603
        have hw : |(1131603727/2500000000 : ℝ)|=(1131603727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172210101/10000000000 : ℝ)|^2115 ≤ (31558089146197/100000000000000 : ℝ)^1603
        have hw : |(4172210101/10000000000 : ℝ)|=(4172210101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1267_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4747449/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16159/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9599/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5487/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14679/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16159/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9599/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16159/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9599/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16159/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9599/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16159/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9599/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16159/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9599/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16159/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9599/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9599/100000 : ℝ) ^ (8459/2048 : ℝ) ≤ (3127416048062471/50000000000000000000 : ℝ) := by
    have hpowers : (9599/100000 : ℝ)^8459 ≤ (3127416048062471/50000000000000000000 : ℝ)^2048 := by
      have hnat : (9599 : ℕ)^8459*50000000000000000000^2048 ≤ 3127416048062471^2048*100000^8459 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9599 100000 3127416048062471 50000000000000000000 8459 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9599/100000 : ℝ)) (X := (3127416048062471/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16159/100000 : ℝ) ^ (8459/2048 : ℝ) ≤ (53759850692412521/100000000000000000000 : ℝ) := by
    have hpowers : (16159/100000 : ℝ)^8459 ≤ (53759850692412521/100000000000000000000 : ℝ)^2048 := by
      have hnat : (16159 : ℕ)^8459*100000000000000000000^2048 ≤ 53759850692412521^2048*100000^8459 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16159 100000 53759850692412521 100000000000000000000 8459 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16159/100000 : ℝ)) (X := (53759850692412521/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003127416048062471/25000000000000000000 : ℝ) ≤ (2000060571173551/2000000000000000 : ℝ) ^ (8459/2048 : ℝ) := by
    have hpowers : (25003127416048062471/25000000000000000000 : ℝ)^2048 ≤ (2000060571173551/2000000000000000 : ℝ)^8459 := by
      have hnat : (25003127416048062471 : ℕ)^2048*2000000000000000^8459 ≤ 2000060571173551^8459*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003127416048062471 25000000000000000000 2000060571173551 2000000000000000 2048 8459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000060571173551/2000000000000000 : ℝ)) (X := (25003127416048062471/25000000000000000000 : ℝ)) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100060014682788537463/100000000000000000000 : ℝ) ≤ (2000290535826001/2000000000000000 : ℝ) ^ (8459/2048 : ℝ) := by
    have hpowers : (100060014682788537463/100000000000000000000 : ℝ)^2048 ≤ (2000290535826001/2000000000000000 : ℝ)^8459 := by
      have hnat : (100060014682788537463 : ℕ)^2048*2000000000000000^8459 ≤ 2000290535826001^8459*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100060014682788537463 100000000000000000000 2000290535826001 2000000000000000 2048 8459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000290535826001/2000000000000000 : ℝ)) (X := (100060014682788537463/100000000000000000000 : ℝ)) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50053759850692412521/50000000000000000000 : ℝ) ≤ (2000520500478451/2000000000000000 : ℝ) ^ (8459/2048 : ℝ) := by
    have hpowers : (50053759850692412521/50000000000000000000 : ℝ)^2048 ≤ (2000520500478451/2000000000000000 : ℝ)^8459 := by
      have hnat : (50053759850692412521 : ℕ)^2048*2000000000000000^8459 ≤ 2000520500478451^8459*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50053759850692412521 50000000000000000000 2000520500478451 2000000000000000 2048 8459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000520500478451/2000000000000000 : ℝ)) (X := (50053759850692412521/50000000000000000000 : ℝ)) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3127416048062471/50000000000000000000 : ℝ) ≤ ((655799124275037973/656000000000000000 : ℝ)+2*(4599293049/2624000000000 : ℝ)*(9599/100000 : ℝ))^(8459/2048 : ℝ) := by
    rw [show (655799124275037973/656000000000000000 : ℝ)+2*(4599293049/2624000000000 : ℝ)*(9599/100000 : ℝ)=(2000060571173551/2000000000000000 : ℝ) by norm_num, show 1+2*(3127416048062471/50000000000000000000 : ℝ)=(25003127416048062471/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(53759850692412521/100000000000000000000 : ℝ)+(3127416048062471/50000000000000000000 : ℝ) ≤ ((655799124275037973/656000000000000000 : ℝ)+(4599293049/2624000000000 : ℝ)*((16159/100000 : ℝ)+(9599/100000 : ℝ)))^(8459/2048 : ℝ) := by
    rw [show (655799124275037973/656000000000000000 : ℝ)+(4599293049/2624000000000 : ℝ)*((16159/100000 : ℝ)+(9599/100000 : ℝ))=(2000290535826001/2000000000000000 : ℝ) by norm_num, show 1+(53759850692412521/100000000000000000000 : ℝ)+(3127416048062471/50000000000000000000 : ℝ)=(100060014682788537463/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(53759850692412521/100000000000000000000 : ℝ) ≤ ((655799124275037973/656000000000000000 : ℝ)+2*(4599293049/2624000000000 : ℝ)*(16159/100000 : ℝ))^(8459/2048 : ℝ) := by
    rw [show (655799124275037973/656000000000000000 : ℝ)+2*(4599293049/2624000000000 : ℝ)*(16159/100000 : ℝ)=(2000520500478451/2000000000000000 : ℝ) by norm_num, show 1+2*(53759850692412521/100000000000000000000 : ℝ)=(50053759850692412521/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (655799124275037973/656000000000000000 : ℝ)*(X 1 0+X 2 0)+(4599293049/2624000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8459/2048 : ℝ)) (lo := (9599/100000 : ℝ)) (hi := (16159/100000 : ℝ)) (c := (655799124275037973/656000000000000000 : ℝ)) (alpha := (4599293049/2624000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (655799124275037973/656000000000000000 : ℝ)*(X 0 1+X 2 1)+(4599293049/2624000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8459/2048 : ℝ)) (lo := (9599/100000 : ℝ)) (hi := (16159/100000 : ℝ)) (c := (655799124275037973/656000000000000000 : ℝ)) (alpha := (4599293049/2624000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (655799124275037973/656000000000000000 : ℝ)*(X 0 2+X 1 2)+(4599293049/2624000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8459/2048 : ℝ)) (lo := (9599/100000 : ℝ)) (hi := (16159/100000 : ℝ)) (c := (655799124275037973/656000000000000000 : ℝ)) (alpha := (4599293049/2624000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2105860443/10000000000 : ℝ)*X 0 0+(135437899/250000000 : ℝ)*X 0 1+(5242489559/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675472593/5000000000 : ℝ)*X 1 0+(-274388549/1250000000 : ℝ)*X 1 1+(65531121/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350945173/10000000000 : ℝ)*X 2 0+(1310622539/2500000000 : ℝ)*X 2 1+(-2195107781/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((217288691/500000000 : ℝ)*X 0 0+(834185287/2000000000 : ℝ)*X 0 1+(2263846343/5000000000 : ℝ)*X 0 2+(217288691/500000000 : ℝ)*X 1 0+(834185287/2000000000 : ℝ)*X 1 1+(2263846343/5000000000 : ℝ)*X 1 2+(217288691/500000000 : ℝ)*X 2 0+(834185287/2000000000 : ℝ)*X 2 1+(2263846343/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-210587431/1000000000 : ℝ)*X 0 0+(5243116037/10000000000 : ℝ)*X 0 1+(5416885741/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5306218407/10000000000 : ℝ)*X 1 0+(-2020711597/10000000000 : ℝ)*X 1 1+(5416885577/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2653108861/5000000000 : ℝ)*X 2 0+(270844301/500000000 : ℝ)*X 2 1+(-505177981/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2172900693/5000000000 : ℝ)*X 0 0+(1131603727/2500000000 : ℝ)*X 0 1+(4172210101/10000000000 : ℝ)*X 0 2+(2172900693/5000000000 : ℝ)*X 1 0+(1131603727/2500000000 : ℝ)*X 1 1+(4172210101/10000000000 : ℝ)*X 1 2+(2172900693/5000000000 : ℝ)*X 2 0+(1131603727/2500000000 : ℝ)*X 2 1+(4172210101/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2062422105636506678709/328000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2976829/500000000000 : ℝ)*(base19) + (22885417/12500000000000 : ℝ)*(base23) + (254956419/100000000000000 : ℝ)*(lower2) + (2289749/6250000000000 : ℝ)*(lower3) + (2129112177954783/50000000000000 : ℝ)*(major0) + (2129112177954783/50000000000000 : ℝ)*(major1) + (2129112177954783/50000000000000 : ℝ)*(major2) + (2856724061139173/50000000000000 : ℝ)*(sp0) + (1428367458322671/25000000000000 : ℝ)*(sp1) + (5713479585359567/100000000000000 : ℝ)*(sp2) + (1401480683502783/50000000000000 : ℝ)*(sp3) + (31646164557/100000000000000 : ℝ)*(sp4) + (9339786419/100000000000000 : ℝ)*(sp5) + (7366774911/100000000000000 : ℝ)*(sp7) + (2802968733780477/100000000000000 : ℝ)*(f.failure) + (2856739884221451/50000000000000 : ℝ)*(f.sum) + (331211868531/328000000000000000000000000 : ℝ)*base65 + (290026870233875141/32800000000000000000000000000000 : ℝ)*base68 + (246062546322675141/32800000000000000000000000000000 : ℝ)*base70 + (2921168489324859/32800000000000000000000000000000 : ℝ)*base71 + (771755783179/328000000000000000000000000 : ℝ)*base73 + (203230255267724859/32800000000000000000000000000000 : ℝ)*base75 + (143798424865875141/32800000000000000000000000000000 : ℝ)*base78 + (288800644163724859/32800000000000000000000000000000 : ℝ)*base79 + (291423253191/65600000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1996827/312500000000000000000 : ℝ)*base90 + (1996827/312500000000000000000 : ℝ)*base92 + (1996827/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3156806314297805511999/656000000000000000000000000 : ℝ) := by norm_num
    linear_combination (293544543/10000000000000 : ℝ)*(base19) + (259867573/12500000000000 : ℝ)*(base23) + (11666843/25000000000000 : ℝ)*(upper3) + (4850827/10000000000000 : ℝ)*(lower4) + (229001739/50000000000000 : ℝ)*(upper5) + (4288982976086281/100000000000000 : ℝ)*(major0) + (4288982976086281/100000000000000 : ℝ)*(major1) + (4288982976086281/100000000000000 : ℝ)*(major2) + (69055693027/100000000000000 : ℝ)*(sp1) + (22366093857/50000000000000 : ℝ)*(sp2) + (1438687562514247/25000000000000 : ℝ)*(sp4) + (5754678258918531/100000000000000 : ℝ)*(sp5) + (575470343892869/10000000000000 : ℝ)*(sp6) + (1411607770854371/50000000000000 : ℝ)*(sp7) + (1411607770854371/50000000000000 : ℝ)*(f.failure) + (1438687562514247/25000000000000 : ℝ)*(f.sum) + (3073602410747/656000000000000000000000000 : ℝ)*base66 + (62771521963601587/65600000000000000000000000000000 : ℝ)*base68 + (64153407511598413/65600000000000000000000000000000 : ℝ)*base69 + (620521894154001587/65600000000000000000000000000000 : ℝ)*base72 + (61083323011/26240000000000000000000000 : ℝ)*base74 + (145970997593198413/65600000000000000000000000000000 : ℝ)*base75 + (338798139086801587/65600000000000000000000000000000 : ℝ)*base78 + (89398132839598413/65600000000000000000000000000000 : ℝ)*base79 + (1109734113157/656000000000000000000000000 : ℝ)*base81 + (1312921/156250000000000000000 : ℝ)*base90 + (1312921/156250000000000000000 : ℝ)*base92 + (1312921/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1267_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4747449/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16159/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9599/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5487/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14679/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1267_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1267_s4_0 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2108000801/10000000000 : ℝ)*x 0 + (5396506759/10000000000 : ℝ)*x 1 + (526209573/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2108000801/10000000000 : ℝ)^2115 ≤ (1282077671927/10000000000000 : ℝ)^1603 := by
    have hnat : (2108000801 : ℕ)^2115*10000000000000^1603 ≤ 1282077671927^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108000801 10000000000 1282077671927 10000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396506759/10000000000 : ℝ)^2115 ≤ (44314844427967/100000000000000 : ℝ)^1603 := by
    have hnat : (5396506759 : ℕ)^2115*100000000000000^1603 ≤ 44314844427967^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396506759 10000000000 44314844427967 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526209573/1000000000 : ℝ)^2115 ≤ (21432189419171/50000000000000 : ℝ)^1603 := by
    have hnat : (526209573 : ℕ)^2115*50000000000000^1603 ≤ 21432189419171^1603*1000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526209573 1000000000 21432189419171 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2108000801/10000000000 : ℝ), (5396506759/10000000000 : ℝ), (526209573/1000000000 : ℝ)] ![(1282077671927/10000000000000 : ℝ), (44314844427967/100000000000000 : ℝ), (21432189419171/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2108000801/10000000000 : ℝ)|^2115 ≤ (1282077671927/10000000000000 : ℝ)^1603
        have hw : |(-2108000801/10000000000 : ℝ)|=(2108000801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396506759/10000000000 : ℝ)|^2115 ≤ (44314844427967/100000000000000 : ℝ)^1603
        have hw : |(5396506759/10000000000 : ℝ)|=(5396506759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526209573/1000000000 : ℝ)|^2115 ≤ (21432189419171/50000000000000 : ℝ)^1603
        have hw : |(526209573/1000000000 : ℝ)|=(526209573/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s4_1 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336409403/2500000000 : ℝ)*x 0 + (-435245961/2000000000 : ℝ)*x 1 + (1052419141/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336409403/2500000000 : ℝ)^2115 ≤ (21882264221079/50000000000000 : ℝ)^1603 := by
    have hnat : (1336409403 : ℕ)^2115*50000000000000^1603 ≤ 21882264221079^1603*2500000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336409403 2500000000 21882264221079 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (435245961/2000000000 : ℝ)^2115 ≤ (534843719063/4000000000000 : ℝ)^1603 := by
    have hnat : (435245961 : ℕ)^2115*4000000000000^1603 ≤ 534843719063^1603*2000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435245961 2000000000 534843719063 4000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052419141/2000000000 : ℝ)^2115 ≤ (857287571393/2000000000000 : ℝ)^1603 := by
    have hnat : (1052419141 : ℕ)^2115*2000000000000^1603 ≤ 857287571393^1603*2000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052419141 2000000000 857287571393 2000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336409403/2500000000 : ℝ), (-435245961/2000000000 : ℝ), (1052419141/2000000000 : ℝ)] ![(21882264221079/50000000000000 : ℝ), (534843719063/4000000000000 : ℝ), (857287571393/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336409403/2500000000 : ℝ)|^2115 ≤ (21882264221079/50000000000000 : ℝ)^1603
        have hw : |(1336409403/2500000000 : ℝ)|=(1336409403/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-435245961/2000000000 : ℝ)|^2115 ≤ (534843719063/4000000000000 : ℝ)^1603
        have hw : |(-435245961/2000000000 : ℝ)|=(435245961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052419141/2000000000 : ℝ)|^2115 ≤ (857287571393/2000000000000 : ℝ)^1603
        have hw : |(1052419141/2000000000 : ℝ)|=(1052419141/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s4_2 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5345637663/10000000000 : ℝ)*x 0 + (1052419131/2000000000 : ℝ)*x 1 + (-2176229803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345637663/10000000000 : ℝ)^2115 ≤ (21882264496527/50000000000000 : ℝ)^1603 := by
    have hnat : (5345637663 : ℕ)^2115*50000000000000^1603 ≤ 21882264496527^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345637663 10000000000 21882264496527 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052419131/2000000000 : ℝ)^2115 ≤ (21432189016133/50000000000000 : ℝ)^1603 := by
    have hnat : (1052419131 : ℕ)^2115*50000000000000^1603 ≤ 21432189016133^1603*2000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052419131 2000000000 21432189016133 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2176229803/10000000000 : ℝ)^2115 ≤ (13371092960361/100000000000000 : ℝ)^1603 := by
    have hnat : (2176229803 : ℕ)^2115*100000000000000^1603 ≤ 13371092960361^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176229803 10000000000 13371092960361 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345637663/10000000000 : ℝ), (1052419131/2000000000 : ℝ), (-2176229803/10000000000 : ℝ)] ![(21882264496527/50000000000000 : ℝ), (21432189016133/50000000000000 : ℝ), (13371092960361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345637663/10000000000 : ℝ)|^2115 ≤ (21882264496527/50000000000000 : ℝ)^1603
        have hw : |(5345637663/10000000000 : ℝ)|=(5345637663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052419131/2000000000 : ℝ)|^2115 ≤ (21432189016133/50000000000000 : ℝ)^1603
        have hw : |(1052419131/2000000000 : ℝ)|=(1052419131/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2176229803/10000000000 : ℝ)|^2115 ≤ (13371092960361/100000000000000 : ℝ)^1603
        have hw : |(-2176229803/10000000000 : ℝ)|=(2176229803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s4_3 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1086764961/2500000000 : ℝ)*x 0 + (4212156549/10000000000 : ℝ)*x 1 + (2243067853/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086764961/2500000000 : ℝ)^2115 ≤ (1665731113157/5000000000000 : ℝ)^1603 := by
    have hnat : (1086764961 : ℕ)^2115*5000000000000^1603 ≤ 1665731113157^1603*2500000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086764961 2500000000 1665731113157 5000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4212156549/10000000000 : ℝ)^2115 ≤ (1278294181161/4000000000000 : ℝ)^1603 := by
    have hnat : (4212156549 : ℕ)^2115*4000000000000^1603 ≤ 1278294181161^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4212156549 10000000000 1278294181161 4000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2243067853/5000000000 : ℝ)^2115 ≤ (4341002897823/12500000000000 : ℝ)^1603 := by
    have hnat : (2243067853 : ℕ)^2115*12500000000000^1603 ≤ 4341002897823^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243067853 5000000000 4341002897823 12500000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1086764961/2500000000 : ℝ), (4212156549/10000000000 : ℝ), (2243067853/5000000000 : ℝ)] ![(1665731113157/5000000000000 : ℝ), (1278294181161/4000000000000 : ℝ), (4341002897823/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1086764961/2500000000 : ℝ)|^2115 ≤ (1665731113157/5000000000000 : ℝ)^1603
        have hw : |(1086764961/2500000000 : ℝ)|=(1086764961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4212156549/10000000000 : ℝ)|^2115 ≤ (1278294181161/4000000000000 : ℝ)^1603
        have hw : |(4212156549/10000000000 : ℝ)|=(4212156549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2243067853/5000000000 : ℝ)|^2115 ≤ (4341002897823/12500000000000 : ℝ)^1603
        have hw : |(2243067853/5000000000 : ℝ)|=(2243067853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s4_4 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2108007001/10000000000 : ℝ)*x 0 + (2631232953/5000000000 : ℝ)*x 1 + (5396134953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2108007001/10000000000 : ℝ)^2115 ≤ (12820826471473/100000000000000 : ℝ)^1603 := by
    have hnat : (2108007001 : ℕ)^2115*100000000000000^1603 ≤ 12820826471473^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108007001 10000000000 12820826471473 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631232953/5000000000 : ℝ)^2115 ≤ (42868357415423/100000000000000 : ℝ)^1603 := by
    have hnat : (2631232953 : ℕ)^2115*100000000000000^1603 ≤ 42868357415423^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631232953 5000000000 42868357415423 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396134953/10000000000 : ℝ)^2115 ≤ (22155408049319/50000000000000 : ℝ)^1603 := by
    have hnat : (5396134953 : ℕ)^2115*50000000000000^1603 ≤ 22155408049319^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396134953 10000000000 22155408049319 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2108007001/10000000000 : ℝ), (2631232953/5000000000 : ℝ), (5396134953/10000000000 : ℝ)] ![(12820826471473/100000000000000 : ℝ), (42868357415423/100000000000000 : ℝ), (22155408049319/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2108007001/10000000000 : ℝ)|^2115 ≤ (12820826471473/100000000000000 : ℝ)^1603
        have hw : |(-2108007001/10000000000 : ℝ)|=(2108007001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631232953/5000000000 : ℝ)|^2115 ≤ (42868357415423/100000000000000 : ℝ)^1603
        have hw : |(2631232953/5000000000 : ℝ)|=(2631232953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396134953/10000000000 : ℝ)|^2115 ≤ (22155408049319/50000000000000 : ℝ)^1603
        have hw : |(5396134953/10000000000 : ℝ)|=(5396134953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s4_5 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2655643063/5000000000 : ℝ)*x 0 + (-1021095309/5000000000 : ℝ)*x 1 + (2698067621/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655643063/5000000000 : ℝ)^2115 ≤ (21696924482197/50000000000000 : ℝ)^1603 := by
    have hnat : (2655643063 : ℕ)^2115*50000000000000^1603 ≤ 21696924482197^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655643063 5000000000 21696924482197 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1021095309/5000000000 : ℝ)^2115 ≤ (6147665895977/50000000000000 : ℝ)^1603 := by
    have hnat : (1021095309 : ℕ)^2115*50000000000000^1603 ≤ 6147665895977^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021095309 5000000000 6147665895977 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698067621/5000000000 : ℝ)^2115 ≤ (11077704807443/25000000000000 : ℝ)^1603 := by
    have hnat : (2698067621 : ℕ)^2115*25000000000000^1603 ≤ 11077704807443^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698067621 5000000000 11077704807443 25000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655643063/5000000000 : ℝ), (-1021095309/5000000000 : ℝ), (2698067621/5000000000 : ℝ)] ![(21696924482197/50000000000000 : ℝ), (6147665895977/50000000000000 : ℝ), (11077704807443/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655643063/5000000000 : ℝ)|^2115 ≤ (21696924482197/50000000000000 : ℝ)^1603
        have hw : |(2655643063/5000000000 : ℝ)|=(2655643063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1021095309/5000000000 : ℝ)|^2115 ≤ (6147665895977/50000000000000 : ℝ)^1603
        have hw : |(-1021095309/5000000000 : ℝ)|=(1021095309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698067621/5000000000 : ℝ)|^2115 ≤ (11077704807443/25000000000000 : ℝ)^1603
        have hw : |(2698067621/5000000000 : ℝ)|=(2698067621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s4_6 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2655643019/5000000000 : ℝ)*x 0 + (1349033929/2500000000 : ℝ)*x 1 + (-2042190091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655643019/5000000000 : ℝ)^2115 ≤ (5424231001973/12500000000000 : ℝ)^1603 := by
    have hnat : (2655643019 : ℕ)^2115*12500000000000^1603 ≤ 5424231001973^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655643019 5000000000 5424231001973 12500000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349033929/2500000000 : ℝ)^2115 ≤ (8862164873053/20000000000000 : ℝ)^1603 := by
    have hnat : (1349033929 : ℕ)^2115*20000000000000^1603 ≤ 8862164873053^1603*2500000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349033929 2500000000 8862164873053 20000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2042190091/10000000000 : ℝ)^2115 ≤ (12295327605643/100000000000000 : ℝ)^1603 := by
    have hnat : (2042190091 : ℕ)^2115*100000000000000^1603 ≤ 12295327605643^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2042190091 10000000000 12295327605643 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655643019/5000000000 : ℝ), (1349033929/2500000000 : ℝ), (-2042190091/10000000000 : ℝ)] ![(5424231001973/12500000000000 : ℝ), (8862164873053/20000000000000 : ℝ), (12295327605643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655643019/5000000000 : ℝ)|^2115 ≤ (5424231001973/12500000000000 : ℝ)^1603
        have hw : |(2655643019/5000000000 : ℝ)|=(2655643019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349033929/2500000000 : ℝ)|^2115 ≤ (8862164873053/20000000000000 : ℝ)^1603
        have hw : |(1349033929/2500000000 : ℝ)|=(1349033929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2042190091/10000000000 : ℝ)|^2115 ≤ (12295327605643/100000000000000 : ℝ)^1603
        have hw : |(-2042190091/10000000000 : ℝ)|=(2042190091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s4_7 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2173535963/5000000000 : ℝ)*x 0 + (560672727/1250000000 : ℝ)*x 1 + (4212913521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173535963/5000000000 : ℝ)^2115 ≤ (4164343053811/12500000000000 : ℝ)^1603 := by
    have hnat : (2173535963 : ℕ)^2115*12500000000000^1603 ≤ 4164343053811^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173535963 5000000000 4164343053811 12500000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (560672727/1250000000 : ℝ)^2115 ≤ (3472032335799/10000000000000 : ℝ)^1603 := by
    have hnat : (560672727 : ℕ)^2115*10000000000000^1603 ≤ 3472032335799^1603*1250000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560672727 1250000000 3472032335799 10000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4212913521/10000000000 : ℝ)^2115 ≤ (15982466097393/50000000000000 : ℝ)^1603 := by
    have hnat : (4212913521 : ℕ)^2115*50000000000000^1603 ≤ 15982466097393^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4212913521 10000000000 15982466097393 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2173535963/5000000000 : ℝ), (560672727/1250000000 : ℝ), (4212913521/10000000000 : ℝ)] ![(4164343053811/12500000000000 : ℝ), (3472032335799/10000000000000 : ℝ), (15982466097393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2173535963/5000000000 : ℝ)|^2115 ≤ (4164343053811/12500000000000 : ℝ)^1603
        have hw : |(2173535963/5000000000 : ℝ)|=(2173535963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(560672727/1250000000 : ℝ)|^2115 ≤ (3472032335799/10000000000000 : ℝ)^1603
        have hw : |(560672727/1250000000 : ℝ)|=(560672727/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4212913521/10000000000 : ℝ)|^2115 ≤ (15982466097393/50000000000000 : ℝ)^1603
        have hw : |(4212913521/10000000000 : ℝ)|=(4212913521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1267_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4747449/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14679/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5487/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (356/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14239/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14679/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5487/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14679/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5487/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14679/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5487/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14679/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5487/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14679/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5487/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14679/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5487/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5487/50000 : ℝ) ^ (8459/2048 : ℝ) ≤ (10873044191223393/100000000000000000000 : ℝ) := by
    have hpowers : (5487/50000 : ℝ)^8459 ≤ (10873044191223393/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5487 : ℕ)^8459*100000000000000000000^2048 ≤ 10873044191223393^2048*50000^8459 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5487 50000 10873044191223393 100000000000000000000 8459 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5487/50000 : ℝ)) (X := (10873044191223393/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14679/100000 : ℝ) ^ (8459/2048 : ℝ) ≤ (3615323709838523/10000000000000000000 : ℝ) := by
    have hpowers : (14679/100000 : ℝ)^8459 ≤ (3615323709838523/10000000000000000000 : ℝ)^2048 := by
      have hnat : (14679 : ℕ)^8459*10000000000000000000^2048 ≤ 3615323709838523^2048*100000^8459 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14679 100000 3615323709838523 10000000000000000000 8459 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14679/100000 : ℝ)) (X := (3615323709838523/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010873044191223393/50000000000000000000 : ℝ) ≤ (500026322449137/500000000000000 : ℝ) ^ (8459/2048 : ℝ) := by
    have hpowers : (50010873044191223393/50000000000000000000 : ℝ)^2048 ≤ (500026322449137/500000000000000 : ℝ)^8459 := by
      have hnat : (50010873044191223393 : ℕ)^2048*500000000000000^8459 ≤ 500026322449137^8459*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010873044191223393 50000000000000000000 500026322449137 500000000000000 2048 8459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500026322449137/500000000000000 : ℝ)) (X := (50010873044191223393/50000000000000000000 : ℝ)) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047026281289608623/100000000000000000000 : ℝ) ≤ (10001138345738447/10000000000000000 : ℝ) ^ (8459/2048 : ℝ) := by
    have hpowers : (100047026281289608623/100000000000000000000 : ℝ)^2048 ≤ (10001138345738447/10000000000000000 : ℝ)^8459 := by
      have hnat : (100047026281289608623 : ℕ)^2048*10000000000000000^8459 ≤ 10001138345738447^8459*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047026281289608623 100000000000000000000 10001138345738447 10000000000000000 2048 8459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001138345738447/10000000000000000 : ℝ)) (X := (100047026281289608623/100000000000000000000 : ℝ)) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003615323709838523/5000000000000000000 : ℝ) ≤ (5000875121247077/5000000000000000 : ℝ) ^ (8459/2048 : ℝ) := by
    have hpowers : (5003615323709838523/5000000000000000000 : ℝ)^2048 ≤ (5000875121247077/5000000000000000 : ℝ)^8459 := by
      have hnat : (5003615323709838523 : ℕ)^2048*5000000000000000^8459 ≤ 5000875121247077^8459*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003615323709838523 5000000000000000000 5000875121247077 5000000000000000 2048 8459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000875121247077/5000000000000000 : ℝ)) (X := (5003615323709838523/5000000000000000000 : ℝ)) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10873044191223393/100000000000000000000 : ℝ) ≤ ((385817922744654109/385937500000000000 : ℝ)+2*(611896755707/370500000000000 : ℝ)*(5487/50000 : ℝ))^(8459/2048 : ℝ) := by
    rw [show (385817922744654109/385937500000000000 : ℝ)+2*(611896755707/370500000000000 : ℝ)*(5487/50000 : ℝ)=(500026322449137/500000000000000 : ℝ) by norm_num, show 1+2*(10873044191223393/100000000000000000000 : ℝ)=(50010873044191223393/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3615323709838523/10000000000000000000 : ℝ)+(10873044191223393/100000000000000000000 : ℝ) ≤ ((385817922744654109/385937500000000000 : ℝ)+(611896755707/370500000000000 : ℝ)*((14679/100000 : ℝ)+(5487/50000 : ℝ)))^(8459/2048 : ℝ) := by
    rw [show (385817922744654109/385937500000000000 : ℝ)+(611896755707/370500000000000 : ℝ)*((14679/100000 : ℝ)+(5487/50000 : ℝ))=(10001138345738447/10000000000000000 : ℝ) by norm_num, show 1+(3615323709838523/10000000000000000000 : ℝ)+(10873044191223393/100000000000000000000 : ℝ)=(100047026281289608623/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3615323709838523/10000000000000000000 : ℝ) ≤ ((385817922744654109/385937500000000000 : ℝ)+2*(611896755707/370500000000000 : ℝ)*(14679/100000 : ℝ))^(8459/2048 : ℝ) := by
    rw [show (385817922744654109/385937500000000000 : ℝ)+2*(611896755707/370500000000000 : ℝ)*(14679/100000 : ℝ)=(5000875121247077/5000000000000000 : ℝ) by norm_num, show 1+2*(3615323709838523/10000000000000000000 : ℝ)=(5003615323709838523/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (385817922744654109/385937500000000000 : ℝ)*(X 1 0+X 2 0)+(611896755707/370500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8459/2048 : ℝ)) (lo := (5487/50000 : ℝ)) (hi := (14679/100000 : ℝ)) (c := (385817922744654109/385937500000000000 : ℝ)) (alpha := (611896755707/370500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (385817922744654109/385937500000000000 : ℝ)*(X 0 1+X 2 1)+(611896755707/370500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8459/2048 : ℝ)) (lo := (5487/50000 : ℝ)) (hi := (14679/100000 : ℝ)) (c := (385817922744654109/385937500000000000 : ℝ)) (alpha := (611896755707/370500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (385817922744654109/385937500000000000 : ℝ)*(X 0 2+X 1 2)+(611896755707/370500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8459/2048 : ℝ)) (lo := (5487/50000 : ℝ)) (hi := (14679/100000 : ℝ)) (c := (385817922744654109/385937500000000000 : ℝ)) (alpha := (611896755707/370500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2108000801/10000000000 : ℝ)*X 0 0+(5396506759/10000000000 : ℝ)*X 0 1+(526209573/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336409403/2500000000 : ℝ)*X 1 0+(-435245961/2000000000 : ℝ)*X 1 1+(1052419141/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345637663/10000000000 : ℝ)*X 2 0+(1052419131/2000000000 : ℝ)*X 2 1+(-2176229803/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1086764961/2500000000 : ℝ)*X 0 0+(4212156549/10000000000 : ℝ)*X 0 1+(2243067853/5000000000 : ℝ)*X 0 2+(1086764961/2500000000 : ℝ)*X 1 0+(4212156549/10000000000 : ℝ)*X 1 1+(2243067853/5000000000 : ℝ)*X 1 2+(1086764961/2500000000 : ℝ)*X 2 0+(4212156549/10000000000 : ℝ)*X 2 1+(2243067853/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2108007001/10000000000 : ℝ)*X 0 0+(2631232953/5000000000 : ℝ)*X 0 1+(5396134953/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655643063/5000000000 : ℝ)*X 1 0+(-1021095309/5000000000 : ℝ)*X 1 1+(2698067621/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655643019/5000000000 : ℝ)*X 2 0+(1349033929/2500000000 : ℝ)*X 2 1+(-2042190091/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2173535963/5000000000 : ℝ)*X 0 0+(560672727/1250000000 : ℝ)*X 0 1+(4212913521/10000000000 : ℝ)*X 0 2+(2173535963/5000000000 : ℝ)*X 1 0+(560672727/1250000000 : ℝ)*X 1 1+(4212913521/10000000000 : ℝ)*X 1 2+(2173535963/5000000000 : ℝ)*X 2 0+(560672727/1250000000 : ℝ)*X 2 1+(4212913521/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (59436206187437335065021339/9648437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (103251319/10000000000000 : ℝ)*(base19) + (1093556567/100000000000000 : ℝ)*(base23) + (109014783/100000000000000 : ℝ)*(upper3) + (83/1562500000 : ℝ)*(upper4) + (117540651/100000000000000 : ℝ)*(upper5) + (693116147385621/12500000000000 : ℝ)*(major0) + (693116147385621/12500000000000 : ℝ)*(major1) + (693116147385621/12500000000000 : ℝ)*(major2) + (3719945622097203/50000000000000 : ℝ)*(sp0) + (7439917187388781/100000000000000 : ℝ)*(sp1) + (1859979281586351/25000000000000 : ℝ)*(sp2) + (364992615595877/10000000000000 : ℝ)*(sp3) + (5395141513/20000000000000 : ℝ)*(sp4) + (1377696953/10000000000000 : ℝ)*(sp7) + (36499399329283/1000000000000 : ℝ)*(f.failure) + (7439918219901971/100000000000000 : ℝ)*(f.sum) + (40736491718783/6175000000000000000000000000 : ℝ)*base66 + (595632624000249/39062500000000000000000000000 : ℝ)*base67 + (272058816672373/78125000000000000000000000000 : ℝ)*base69 + (61526736293031/9765625000000000000000000000 : ℝ)*base71 + (12787984577417/6175000000000000000000000000 : ℝ)*base73 + (521673978640127/78125000000000000000000000000 : ℝ)*base76 + (23981532794953/4882812500000000000000000000 : ℝ)*base77 + (53060335875249/39062500000000000000000000000 : ℝ)*base79 + (14919785395679/3087500000000000000000000000 : ℝ)*base82 + (933/3125000000000000000 : ℝ)*base90 + (933/3125000000000000000 : ℝ)*base92 + (933/3125000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1547913456419508855748403/192968750000000000000000000000 : ℝ) := by norm_num
    linear_combination (243335063/50000000000000 : ℝ)*(base19) + (400067/39062500000 : ℝ)*(base23) + (180531869/100000000000000 : ℝ)*(upper2) + (440261291/100000000000000 : ℝ)*(upper3) + (249811/1562500000000 : ℝ)*(upper4) + (223026065712103/4000000000000 : ℝ)*(major0) + (223026065712103/4000000000000 : ℝ)*(major1) + (223026065712103/4000000000000 : ℝ)*(major2) + (6796346161/12500000000000 : ℝ)*(sp2) + (808747763/50000000000000 : ℝ)*(sp3) + (3740570038644339/50000000000000 : ℝ)*(sp4) + (935142448827319/12500000000000 : ℝ)*(sp5) + (7481084682347871/100000000000000 : ℝ)*(sp6) + (917540330858769/25000000000000 : ℝ)*(sp7) + (1835081470465301/50000000000000 : ℝ)*(f.failure) + (3740570038644339/50000000000000 : ℝ)*(f.sum) + (2898548987099/741000000000000000000000000 : ℝ)*base65 + (60703965299551/9375000000000000000000000000 : ℝ)*base68 + (21998665687949/9375000000000000000000000000 : ℝ)*base69 + (41826969805801/9375000000000000000000000000 : ℝ)*base72 + (2684079125207/741000000000000000000000000 : ℝ)*base73 + (111119279155801/9375000000000000000000000000 : ℝ)*base76 + (37345808774551/9375000000000000000000000000 : ℝ)*base78 + (228864202874551/9375000000000000000000000000 : ℝ)*base80 + (1964055424207/370500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (670351/156250000000000000000 : ℝ)*base90 + (670351/156250000000000000000 : ℝ)*base92 + (670351/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1267_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4747449/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14679/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5487/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (356/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1267_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1267_s5_0 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1054206717/5000000000 : ℝ)*x 0 + (5391813581/10000000000 : ℝ)*x 1 + (210660701/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054206717/5000000000 : ℝ)^2115 ≤ (3206022003709/25000000000000 : ℝ)^1603 := by
    have hnat : (1054206717 : ℕ)^2115*25000000000000^1603 ≤ 3206022003709^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054206717 5000000000 3206022003709 25000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391813581/10000000000 : ℝ)^2115 ≤ (4426400273011/10000000000000 : ℝ)^1603 := by
    have hnat : (5391813581 : ℕ)^2115*10000000000000^1603 ≤ 4426400273011^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391813581 10000000000 4426400273011 10000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210660701/400000000 : ℝ)^2115 ≤ (10727977310703/25000000000000 : ℝ)^1603 := by
    have hnat : (210660701 : ℕ)^2115*25000000000000^1603 ≤ 10727977310703^1603*400000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210660701 400000000 10727977310703 25000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1054206717/5000000000 : ℝ), (5391813581/10000000000 : ℝ), (210660701/400000000 : ℝ)] ![(3206022003709/25000000000000 : ℝ), (4426400273011/10000000000000 : ℝ), (10727977310703/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1054206717/5000000000 : ℝ)|^2115 ≤ (3206022003709/25000000000000 : ℝ)^1603
        have hw : |(-1054206717/5000000000 : ℝ)|=(1054206717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391813581/10000000000 : ℝ)|^2115 ≤ (4426400273011/10000000000000 : ℝ)^1603
        have hw : |(5391813581/10000000000 : ℝ)|=(5391813581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210660701/400000000 : ℝ)|^2115 ≤ (10727977310703/25000000000000 : ℝ)^1603
        have hw : |(210660701/400000000 : ℝ)|=(210660701/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s5_1 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344447463/10000000000 : ℝ)*x 0 + (-2171950889/10000000000 : ℝ)*x 1 + (2633258823/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344447463/10000000000 : ℝ)^2115 ≤ (43751673045483/100000000000000 : ℝ)^1603 := by
    have hnat : (5344447463 : ℕ)^2115*100000000000000^1603 ≤ 43751673045483^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344447463 10000000000 43751673045483 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2171950889/10000000000 : ℝ)^2115 ≤ (6668208196131/50000000000000 : ℝ)^1603 := by
    have hnat : (2171950889 : ℕ)^2115*50000000000000^1603 ≤ 6668208196131^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171950889 10000000000 6668208196131 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633258823/5000000000 : ℝ)^2115 ≤ (4291191054363/10000000000000 : ℝ)^1603 := by
    have hnat : (2633258823 : ℕ)^2115*10000000000000^1603 ≤ 4291191054363^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633258823 5000000000 4291191054363 10000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344447463/10000000000 : ℝ), (-2171950889/10000000000 : ℝ), (2633258823/5000000000 : ℝ)] ![(43751673045483/100000000000000 : ℝ), (6668208196131/50000000000000 : ℝ), (4291191054363/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344447463/10000000000 : ℝ)|^2115 ≤ (43751673045483/100000000000000 : ℝ)^1603
        have hw : |(5344447463/10000000000 : ℝ)|=(5344447463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2171950889/10000000000 : ℝ)|^2115 ≤ (6668208196131/50000000000000 : ℝ)^1603
        have hw : |(-2171950889/10000000000 : ℝ)|=(2171950889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633258823/5000000000 : ℝ)|^2115 ≤ (4291191054363/10000000000000 : ℝ)^1603
        have hw : |(2633258823/5000000000 : ℝ)|=(2633258823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s5_2 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (534444759/1000000000 : ℝ)*x 0 + (5266517701/10000000000 : ℝ)*x 1 + (-2171950647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534444759/1000000000 : ℝ)^2115 ≤ (1750066976689/4000000000000 : ℝ)^1603 := by
    have hnat : (534444759 : ℕ)^2115*4000000000000^1603 ≤ 1750066976689^1603*1000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534444759 1000000000 1750066976689 4000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266517701/10000000000 : ℝ)^2115 ≤ (42911911134911/100000000000000 : ℝ)^1603 := by
    have hnat : (5266517701 : ℕ)^2115*100000000000000^1603 ≤ 42911911134911^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266517701 10000000000 42911911134911 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2171950647/10000000000 : ℝ)^2115 ≤ (833525901981/6250000000000 : ℝ)^1603 := by
    have hnat : (2171950647 : ℕ)^2115*6250000000000^1603 ≤ 833525901981^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171950647 10000000000 833525901981 6250000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534444759/1000000000 : ℝ), (5266517701/10000000000 : ℝ), (-2171950647/10000000000 : ℝ)] ![(1750066976689/4000000000000 : ℝ), (42911911134911/100000000000000 : ℝ), (833525901981/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534444759/1000000000 : ℝ)|^2115 ≤ (1750066976689/4000000000000 : ℝ)^1603
        have hw : |(534444759/1000000000 : ℝ)|=(534444759/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266517701/10000000000 : ℝ)|^2115 ≤ (42911911134911/100000000000000 : ℝ)^1603
        have hw : |(5266517701/10000000000 : ℝ)|=(5266517701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2171950647/10000000000 : ℝ)|^2115 ≤ (833525901981/6250000000000 : ℝ)^1603
        have hw : |(-2171950647/10000000000 : ℝ)|=(2171950647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s5_3 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (271706429/625000000 : ℝ)*x 0 + (4221415223/10000000000 : ℝ)*x 1 + (2238407329/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271706429/625000000 : ℝ)^2115 ≤ (666341591697/2000000000000 : ℝ)^1603 := by
    have hnat : (271706429 : ℕ)^2115*2000000000000^1603 ≤ 666341591697^1603*625000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271706429 625000000 666341591697 2000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4221415223/10000000000 : ℝ)^2115 ≤ (16025034156763/50000000000000 : ℝ)^1603 := by
    have hnat : (4221415223 : ℕ)^2115*50000000000000^1603 ≤ 16025034156763^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4221415223 10000000000 16025034156763 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2238407329/5000000000 : ℝ)^2115 ≤ (17316426045411/50000000000000 : ℝ)^1603 := by
    have hnat : (2238407329 : ℕ)^2115*50000000000000^1603 ≤ 17316426045411^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238407329 5000000000 17316426045411 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(271706429/625000000 : ℝ), (4221415223/10000000000 : ℝ), (2238407329/5000000000 : ℝ)] ![(666341591697/2000000000000 : ℝ), (16025034156763/50000000000000 : ℝ), (17316426045411/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(271706429/625000000 : ℝ)|^2115 ≤ (666341591697/2000000000000 : ℝ)^1603
        have hw : |(271706429/625000000 : ℝ)|=(271706429/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4221415223/10000000000 : ℝ)|^2115 ≤ (16025034156763/50000000000000 : ℝ)^1603
        have hw : |(4221415223/10000000000 : ℝ)|=(4221415223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2238407329/5000000000 : ℝ)|^2115 ≤ (17316426045411/50000000000000 : ℝ)^1603
        have hw : |(2238407329/5000000000 : ℝ)|=(2238407329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s5_4 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-421683677/2000000000 : ℝ)*x 0 + (2633419469/5000000000 : ℝ)*x 1 + (5391490899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (421683677/2000000000 : ℝ)^2115 ≤ (12824127746857/100000000000000 : ℝ)^1603 := by
    have hnat : (421683677 : ℕ)^2115*100000000000000^1603 ≤ 12824127746857^1603*2000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421683677 2000000000 12824127746857 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633419469/5000000000 : ℝ)^2115 ≤ (8583072929351/20000000000000 : ℝ)^1603 := by
    have hnat : (2633419469 : ℕ)^2115*20000000000000^1603 ≤ 8583072929351^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633419469 5000000000 8583072929351 20000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391490899/10000000000 : ℝ)^2115 ≤ (44260507600751/100000000000000 : ℝ)^1603 := by
    have hnat : (5391490899 : ℕ)^2115*100000000000000^1603 ≤ 44260507600751^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391490899 10000000000 44260507600751 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-421683677/2000000000 : ℝ), (2633419469/5000000000 : ℝ), (5391490899/10000000000 : ℝ)] ![(12824127746857/100000000000000 : ℝ), (8583072929351/20000000000000 : ℝ), (44260507600751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-421683677/2000000000 : ℝ)|^2115 ≤ (12824127746857/100000000000000 : ℝ)^1603
        have hw : |(-421683677/2000000000 : ℝ)|=(421683677/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633419469/5000000000 : ℝ)|^2115 ≤ (8583072929351/20000000000000 : ℝ)^1603
        have hw : |(2633419469/5000000000 : ℝ)|=(2633419469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391490899/10000000000 : ℝ)|^2115 ≤ (44260507600751/100000000000000 : ℝ)^1603
        have hw : |(5391490899/10000000000 : ℝ)|=(5391490899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s5_5 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1328106267/2500000000 : ℝ)*x 0 + (-2046976969/10000000000 : ℝ)*x 1 + (84242043/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328106267/2500000000 : ℝ)^2115 ≤ (10851531699933/25000000000000 : ℝ)^1603 := by
    have hnat : (1328106267 : ℕ)^2115*25000000000000^1603 ≤ 10851531699933^1603*2500000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328106267 2500000000 10851531699933 25000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2046976969/10000000000 : ℝ)^2115 ≤ (12333367176113/100000000000000 : ℝ)^1603 := by
    have hnat : (2046976969 : ℕ)^2115*100000000000000^1603 ≤ 12333367176113^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2046976969 10000000000 12333367176113 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84242043/156250000 : ℝ)^2115 ≤ (5532563251067/12500000000000 : ℝ)^1603 := by
    have hnat : (84242043 : ℕ)^2115*12500000000000^1603 ≤ 5532563251067^1603*156250000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84242043 156250000 5532563251067 12500000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328106267/2500000000 : ℝ), (-2046976969/10000000000 : ℝ), (84242043/156250000 : ℝ)] ![(10851531699933/25000000000000 : ℝ), (12333367176113/100000000000000 : ℝ), (5532563251067/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328106267/2500000000 : ℝ)|^2115 ≤ (10851531699933/25000000000000 : ℝ)^1603
        have hw : |(1328106267/2500000000 : ℝ)|=(1328106267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2046976969/10000000000 : ℝ)|^2115 ≤ (12333367176113/100000000000000 : ℝ)^1603
        have hw : |(-2046976969/10000000000 : ℝ)|=(2046976969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84242043/156250000 : ℝ)|^2115 ≤ (5532563251067/12500000000000 : ℝ)^1603
        have hw : |(84242043/156250000 : ℝ)|=(84242043/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s5_6 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312425143/10000000000 : ℝ)*x 0 + (1078298091/2000000000 : ℝ)*x 1 + (-255872159/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312425143/10000000000 : ℝ)^2115 ≤ (21703063804131/50000000000000 : ℝ)^1603 := by
    have hnat : (5312425143 : ℕ)^2115*50000000000000^1603 ≤ 21703063804131^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312425143 10000000000 21703063804131 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078298091/2000000000 : ℝ)^2115 ≤ (11065125697903/25000000000000 : ℝ)^1603 := by
    have hnat : (1078298091 : ℕ)^2115*25000000000000^1603 ≤ 11065125697903^1603*2000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078298091 2000000000 11065125697903 25000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (255872159/1250000000 : ℝ)^2115 ≤ (12333369584843/100000000000000 : ℝ)^1603 := by
    have hnat : (255872159 : ℕ)^2115*100000000000000^1603 ≤ 12333369584843^1603*1250000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      255872159 1250000000 12333369584843 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312425143/10000000000 : ℝ), (1078298091/2000000000 : ℝ), (-255872159/1250000000 : ℝ)] ![(21703063804131/50000000000000 : ℝ), (11065125697903/25000000000000 : ℝ), (12333369584843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312425143/10000000000 : ℝ)|^2115 ≤ (21703063804131/50000000000000 : ℝ)^1603
        have hw : |(5312425143/10000000000 : ℝ)|=(5312425143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078298091/2000000000 : ℝ)|^2115 ≤ (11065125697903/25000000000000 : ℝ)^1603
        have hw : |(1078298091/2000000000 : ℝ)|=(1078298091/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-255872159/1250000000 : ℝ)|^2115 ≤ (12333369584843/100000000000000 : ℝ)^1603
        have hw : |(-255872159/1250000000 : ℝ)|=(255872159/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s5_7 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (869462449/2000000000 : ℝ)*x 0 + (1119039807/2500000000 : ℝ)*x 1 + (4222073563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (869462449/2000000000 : ℝ)^2115 ≤ (1332686977707/4000000000000 : ℝ)^1603 := by
    have hnat : (869462449 : ℕ)^2115*4000000000000^1603 ≤ 1332686977707^1603*2000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869462449 2000000000 1332686977707 4000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1119039807/2500000000 : ℝ)^2115 ≤ (8656540576481/25000000000000 : ℝ)^1603 := by
    have hnat : (1119039807 : ℕ)^2115*25000000000000^1603 ≤ 8656540576481^1603*2500000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119039807 2500000000 8656540576481 25000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4222073563/10000000000 : ℝ)^2115 ≤ (16028331611177/50000000000000 : ℝ)^1603 := by
    have hnat : (4222073563 : ℕ)^2115*50000000000000^1603 ≤ 16028331611177^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4222073563 10000000000 16028331611177 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(869462449/2000000000 : ℝ), (1119039807/2500000000 : ℝ), (4222073563/10000000000 : ℝ)] ![(1332686977707/4000000000000 : ℝ), (8656540576481/25000000000000 : ℝ), (16028331611177/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(869462449/2000000000 : ℝ)|^2115 ≤ (1332686977707/4000000000000 : ℝ)^1603
        have hw : |(869462449/2000000000 : ℝ)|=(869462449/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1119039807/2500000000 : ℝ)|^2115 ≤ (8656540576481/25000000000000 : ℝ)^1603
        have hw : |(1119039807/2500000000 : ℝ)|=(1119039807/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4222073563/10000000000 : ℝ)|^2115 ≤ (16028331611177/50000000000000 : ℝ)^1603
        have hw : |(4222073563/10000000000 : ℝ)|=(4222073563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1267_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4747449/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (356/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (5743/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14141/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14239/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (356/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14239/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (356/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14239/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (356/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14239/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (356/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14239/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (356/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14239/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (356/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (356/3125 : ℝ) ^ (8459/2048 : ℝ) ≤ (12688427783851569/100000000000000000000 : ℝ) := by
    have hpowers : (356/3125 : ℝ)^8459 ≤ (12688427783851569/100000000000000000000 : ℝ)^2048 := by
      have hnat : (356 : ℕ)^8459*100000000000000000000^2048 ≤ 12688427783851569^2048*3125^8459 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        356 3125 12688427783851569 100000000000000000000 8459 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (356/3125 : ℝ)) (X := (12688427783851569/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14239/100000 : ℝ) ^ (8459/2048 : ℝ) ≤ (31882778010250467/100000000000000000000 : ℝ) := by
    have hpowers : (14239/100000 : ℝ)^8459 ≤ (31882778010250467/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14239 : ℕ)^8459*100000000000000000000^2048 ≤ 31882778010250467^2048*100000^8459 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14239 100000 31882778010250467 100000000000000000000 8459 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14239/100000 : ℝ)) (X := (31882778010250467/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50012688427783851569/50000000000000000000 : ℝ) ≤ (2000122867485769/2000000000000000 : ℝ) ^ (8459/2048 : ℝ) := by
    have hpowers : (50012688427783851569/50000000000000000000 : ℝ)^2048 ≤ (2000122867485769/2000000000000000 : ℝ)^8459 := by
      have hnat : (50012688427783851569 : ℕ)^2048*2000000000000000^8459 ≤ 2000122867485769^8459*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012688427783851569 50000000000000000000 2000122867485769 2000000000000000 2048 8459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000122867485769/2000000000000000 : ℝ)) (X := (50012688427783851569/50000000000000000000 : ℝ)) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011142801448525509/25000000000000000000 : ℝ) ≤ (250026973169387/250000000000000 : ℝ) ^ (8459/2048 : ℝ) := by
    have hpowers : (25011142801448525509/25000000000000000000 : ℝ)^2048 ≤ (250026973169387/250000000000000 : ℝ)^8459 := by
      have hnat : (25011142801448525509 : ℕ)^2048*250000000000000^8459 ≤ 250026973169387^8459*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011142801448525509 25000000000000000000 250026973169387 250000000000000 2048 8459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250026973169387/250000000000000 : ℝ)) (X := (25011142801448525509/25000000000000000000 : ℝ)) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031882778010250467/50000000000000000000 : ℝ) ≤ (2000308703224423/2000000000000000 : ℝ) ^ (8459/2048 : ℝ) := by
    have hpowers : (50031882778010250467/50000000000000000000 : ℝ)^2048 ≤ (2000308703224423/2000000000000000 : ℝ)^8459 := by
      have hnat : (50031882778010250467 : ℕ)^2048*2000000000000000^8459 ≤ 2000308703224423^8459*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031882778010250467 50000000000000000000 2000308703224423 2000000000000000 2048 8459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000308703224423/2000000000000000 : ℝ)) (X := (50031882778010250467/50000000000000000000 : ℝ)) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(12688427783851569/100000000000000000000 : ℝ) ≤ ((75896436839963173/75920000000000000 : ℝ)+2*(30972623109/18980000000000 : ℝ)*(356/3125 : ℝ))^(8459/2048 : ℝ) := by
    rw [show (75896436839963173/75920000000000000 : ℝ)+2*(30972623109/18980000000000 : ℝ)*(356/3125 : ℝ)=(2000122867485769/2000000000000000 : ℝ) by norm_num, show 1+2*(12688427783851569/100000000000000000000 : ℝ)=(50012688427783851569/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31882778010250467/100000000000000000000 : ℝ)+(12688427783851569/100000000000000000000 : ℝ) ≤ ((75896436839963173/75920000000000000 : ℝ)+(30972623109/18980000000000 : ℝ)*((14239/100000 : ℝ)+(356/3125 : ℝ)))^(8459/2048 : ℝ) := by
    rw [show (75896436839963173/75920000000000000 : ℝ)+(30972623109/18980000000000 : ℝ)*((14239/100000 : ℝ)+(356/3125 : ℝ))=(250026973169387/250000000000000 : ℝ) by norm_num, show 1+(31882778010250467/100000000000000000000 : ℝ)+(12688427783851569/100000000000000000000 : ℝ)=(25011142801448525509/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31882778010250467/100000000000000000000 : ℝ) ≤ ((75896436839963173/75920000000000000 : ℝ)+2*(30972623109/18980000000000 : ℝ)*(14239/100000 : ℝ))^(8459/2048 : ℝ) := by
    rw [show (75896436839963173/75920000000000000 : ℝ)+2*(30972623109/18980000000000 : ℝ)*(14239/100000 : ℝ)=(2000308703224423/2000000000000000 : ℝ) by norm_num, show 1+2*(31882778010250467/100000000000000000000 : ℝ)=(50031882778010250467/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (75896436839963173/75920000000000000 : ℝ)*(X 1 0+X 2 0)+(30972623109/18980000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8459/2048 : ℝ)) (lo := (356/3125 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (75896436839963173/75920000000000000 : ℝ)) (alpha := (30972623109/18980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (75896436839963173/75920000000000000 : ℝ)*(X 0 1+X 2 1)+(30972623109/18980000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8459/2048 : ℝ)) (lo := (356/3125 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (75896436839963173/75920000000000000 : ℝ)) (alpha := (30972623109/18980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (75896436839963173/75920000000000000 : ℝ)*(X 0 2+X 1 2)+(30972623109/18980000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8459/2048 : ℝ)) (lo := (356/3125 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (75896436839963173/75920000000000000 : ℝ)) (alpha := (30972623109/18980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1054206717/5000000000 : ℝ)*X 0 0+(5391813581/10000000000 : ℝ)*X 0 1+(210660701/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344447463/10000000000 : ℝ)*X 1 0+(-2171950889/10000000000 : ℝ)*X 1 1+(2633258823/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534444759/1000000000 : ℝ)*X 2 0+(5266517701/10000000000 : ℝ)*X 2 1+(-2171950647/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((271706429/625000000 : ℝ)*X 0 0+(4221415223/10000000000 : ℝ)*X 0 1+(2238407329/5000000000 : ℝ)*X 0 2+(271706429/625000000 : ℝ)*X 1 0+(4221415223/10000000000 : ℝ)*X 1 1+(2238407329/5000000000 : ℝ)*X 1 2+(271706429/625000000 : ℝ)*X 2 0+(4221415223/10000000000 : ℝ)*X 2 1+(2238407329/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-421683677/2000000000 : ℝ)*X 0 0+(2633419469/5000000000 : ℝ)*X 0 1+(5391490899/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328106267/2500000000 : ℝ)*X 1 0+(-2046976969/10000000000 : ℝ)*X 1 1+(84242043/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312425143/10000000000 : ℝ)*X 2 0+(1078298091/2000000000 : ℝ)*X 2 1+(-255872159/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((869462449/2000000000 : ℝ)*X 0 0+(1119039807/2500000000 : ℝ)*X 0 1+(4222073563/10000000000 : ℝ)*X 0 2+(869462449/2000000000 : ℝ)*X 1 0+(1119039807/2500000000 : ℝ)*X 1 1+(4222073563/10000000000 : ℝ)*X 1 2+(869462449/2000000000 : ℝ)*X 2 0+(1119039807/2500000000 : ℝ)*X 2 1+(4222073563/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (126716246830072823883/18250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1720895483/100000000000000 : ℝ)*(base19) + (1845111437/100000000000000 : ℝ)*(base23) + (34974489/100000000000000 : ℝ)*(lower2) + (207981831/100000000000000 : ℝ)*(upper3) + (589043151/100000000000000 : ℝ)*(upper5) + (5948333921098439/100000000000000 : ℝ)*(major0) + (5948333921098439/100000000000000 : ℝ)*(major1) + (5948333921098439/100000000000000 : ℝ)*(major2) + (1596226189234903/20000000000000 : ℝ)*(sp0) + (3990592745567063/50000000000000 : ℝ)*(sp1) + (1995296341729543/25000000000000 : ℝ)*(sp2) + (783092204376201/20000000000000 : ℝ)*(sp3) + (28132927547/50000000000000 : ℝ)*(sp4) + (387536821/2000000000000 : ℝ)*(sp7) + (1957740199361027/50000000000000 : ℝ)*(f.failure) + (7981187212029609/100000000000000 : ℝ)*(f.sum) + (355199563983/73000000000000000000000000 : ℝ)*base66 + (3235626644984081/584000000000000000000000000000 : ℝ)*base68 + (841583129680081/584000000000000000000000000000 : ℝ)*base70 + (2133265807511919/584000000000000000000000000000 : ℝ)*base71 + (175661363023/36500000000000000000000000 : ℝ)*base74 + (3583897321559919/584000000000000000000000000000 : ℝ)*base75 + (4512177147416081/584000000000000000000000000000 : ℝ)*base78 + (12101016830975919/584000000000000000000000000000 : ℝ)*base79 + (208108745861/73000000000000000000000000 : ℝ)*base82 + (2667377/156250000000000000000 : ℝ)*base90 + (2667377/156250000000000000000 : ℝ)*base92 + (2667377/156250000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (359125889545383487641/73000000000000000000000000 : ℝ) := by norm_num
    linear_combination (163008007/5000000000000 : ℝ)*(base19) + (29295257/781250000000 : ℝ)*(base23) + (64779939/25000000000000 : ℝ)*(upper2) + (18803793/12500000000000 : ℝ)*(upper3) + (464699931/100000000000000 : ℝ)*(upper5) + (5979008079648799/100000000000000 : ℝ)*(major0) + (5979008079648799/100000000000000 : ℝ)*(major1) + (5979008079648799/100000000000000 : ℝ)*(major2) + (385735807/390625000000 : ℝ)*(sp1) + (40134712831/50000000000000 : ℝ)*(sp2) + (8022344385380651/100000000000000 : ℝ)*(sp4) + (50139014855337/625000000000 : ℝ)*(sp5) + (4011130183081047/50000000000000 : ℝ)*(sp6) + (122989737810391/3125000000000 : ℝ)*(sp7) + (122989737810391/3125000000000 : ℝ)*(f.failure) + (8022344385380651/100000000000000 : ℝ)*(f.sum) + (1511643379/36500000000000000000000000 : ℝ)*base66 + (667705965433479/584000000000000000000000000000 : ℝ)*base67 + (316683344929479/584000000000000000000000000000 : ℝ)*base69 + (2449115304214521/584000000000000000000000000000 : ℝ)*base72 + (209639498343/73000000000000000000000000 : ℝ)*base73 + (5793495508502521/584000000000000000000000000000 : ℝ)*base76 + (7675191941958521/584000000000000000000000000000 : ℝ)*base78 + (5239335524137479/584000000000000000000000000000 : ℝ)*base79 + (18454057541/14600000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (339139/39062500000000000000 : ℝ)*base90 + (339139/39062500000000000000 : ℝ)*base92 + (339139/39062500000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1267_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4747449/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (356/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5743/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14141/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1267_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1267_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4747449/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16159/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9599/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5743/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14141/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1267_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1267_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1267_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4747449/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16159/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9599/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5743/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14141/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1267_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

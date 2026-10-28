-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1086_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:54:57.902542+00:00
-- url     : https://prove2.me/submissions/dc9ce077-f7c2-4648-aca3-2deb103d137a

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
theorem support_rectangle_w1086_s0_0 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1909661637/10000000000 : ℝ)*x 0 + (30336821/50000000 : ℝ)*x 1 + (2386674611/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1909661637/10000000000 : ℝ)^8279 ≤ (277052310227/2500000000000 : ℝ)^6231 := by
    have hnat : (1909661637 : ℕ)^8279*2500000000000^6231 ≤ 277052310227^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1909661637 10000000000 277052310227 2500000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (30336821/50000000 : ℝ)^8279 ≤ (51484524127243/100000000000000 : ℝ)^6231 := by
    have hnat : (30336821 : ℕ)^8279*100000000000000^6231 ≤ 51484524127243^6231*50000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30336821 50000000 51484524127243 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2386674611/5000000000 : ℝ)^8279 ≤ (18716691725247/50000000000000 : ℝ)^6231 := by
    have hnat : (2386674611 : ℕ)^8279*50000000000000^6231 ≤ 18716691725247^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2386674611 5000000000 18716691725247 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1909661637/10000000000 : ℝ), (30336821/50000000 : ℝ), (2386674611/5000000000 : ℝ)] ![(277052310227/2500000000000 : ℝ), (51484524127243/100000000000000 : ℝ), (18716691725247/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1909661637/10000000000 : ℝ)|^8279 ≤ (277052310227/2500000000000 : ℝ)^6231
        have hw : |(-1909661637/10000000000 : ℝ)|=(1909661637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(30336821/50000000 : ℝ)|^8279 ≤ (51484524127243/100000000000000 : ℝ)^6231
        have hw : |(30336821/50000000 : ℝ)|=(30336821/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2386674611/5000000000 : ℝ)|^8279 ≤ (18716691725247/50000000000000 : ℝ)^6231
        have hw : |(2386674611/5000000000 : ℝ)|=(2386674611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s0_1 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1103989493/2000000000 : ℝ)*x 0 + (-2653912153/10000000000 : ℝ)*x 1 + (2386674549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1103989493/2000000000 : ℝ)^8279 ≤ (1816244548229/4000000000000 : ℝ)^6231 := by
    have hnat : (1103989493 : ℕ)^8279*4000000000000^6231 ≤ 1816244548229^6231*2000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103989493 2000000000 1816244548229 4000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2653912153/10000000000 : ℝ)^8279 ≤ (17160504122321/100000000000000 : ℝ)^6231 := by
    have hnat : (2653912153 : ℕ)^8279*100000000000000^6231 ≤ 17160504122321^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2653912153 10000000000 17160504122321 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2386674549/5000000000 : ℝ)^8279 ≤ (37433382158449/100000000000000 : ℝ)^6231 := by
    have hnat : (2386674549 : ℕ)^8279*100000000000000^6231 ≤ 37433382158449^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2386674549 5000000000 37433382158449 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1103989493/2000000000 : ℝ), (-2653912153/10000000000 : ℝ), (2386674549/5000000000 : ℝ)] ![(1816244548229/4000000000000 : ℝ), (17160504122321/100000000000000 : ℝ), (37433382158449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1103989493/2000000000 : ℝ)|^8279 ≤ (1816244548229/4000000000000 : ℝ)^6231
        have hw : |(1103989493/2000000000 : ℝ)|=(1103989493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2653912153/10000000000 : ℝ)|^8279 ≤ (17160504122321/100000000000000 : ℝ)^6231
        have hw : |(-2653912153/10000000000 : ℝ)|=(2653912153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2386674549/5000000000 : ℝ)|^8279 ≤ (37433382158449/100000000000000 : ℝ)^6231
        have hw : |(2386674549/5000000000 : ℝ)|=(2386674549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s0_2 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (344996687/625000000 : ℝ)*x 0 + (954669899/2000000000 : ℝ)*x 1 + (-165869517/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (344996687/625000000 : ℝ)^8279 ≤ (567576356701/1250000000000 : ℝ)^6231 := by
    have hnat : (344996687 : ℕ)^8279*1250000000000^6231 ≤ 567576356701^6231*625000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344996687 625000000 567576356701 1250000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (954669899/2000000000 : ℝ)^8279 ≤ (18716693147539/50000000000000 : ℝ)^6231 := by
    have hnat : (954669899 : ℕ)^8279*50000000000000^6231 ≤ 18716693147539^6231*2000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      954669899 2000000000 18716693147539 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (165869517/625000000 : ℝ)^8279 ≤ (17160505144697/100000000000000 : ℝ)^6231 := by
    have hnat : (165869517 : ℕ)^8279*100000000000000^6231 ≤ 17160505144697^6231*625000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165869517 625000000 17160505144697 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(344996687/625000000 : ℝ), (954669899/2000000000 : ℝ), (-165869517/625000000 : ℝ)] ![(567576356701/1250000000000 : ℝ), (18716693147539/50000000000000 : ℝ), (17160505144697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(344996687/625000000 : ℝ)|^8279 ≤ (567576356701/1250000000000 : ℝ)^6231
        have hw : |(344996687/625000000 : ℝ)|=(344996687/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(954669899/2000000000 : ℝ)|^8279 ≤ (18716693147539/50000000000000 : ℝ)^6231
        have hw : |(954669899/2000000000 : ℝ)|=(954669899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-165869517/625000000 : ℝ)|^8279 ≤ (17160505144697/100000000000000 : ℝ)^6231
        have hw : |(-165869517/625000000 : ℝ)|=(165869517/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s0_3 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1051389777/2500000000 : ℝ)*x 0 + (1561908743/5000000000 : ℝ)*x 1 + (2834989321/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051389777/2500000000 : ℝ)^8279 ≤ (15818031626911/50000000000000 : ℝ)^6231 := by
    have hnat : (1051389777 : ℕ)^8279*50000000000000^6231 ≤ 15818031626911^6231*2500000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051389777 2500000000 15818031626911 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1561908743/5000000000 : ℝ)^8279 ≤ (21310779893997/100000000000000 : ℝ)^6231 := by
    have hnat : (1561908743 : ℕ)^8279*100000000000000^6231 ≤ 21310779893997^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1561908743 5000000000 21310779893997 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2834989321/5000000000 : ℝ)^8279 ≤ (23526578420623/50000000000000 : ℝ)^6231 := by
    have hnat : (2834989321 : ℕ)^8279*50000000000000^6231 ≤ 23526578420623^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2834989321 5000000000 23526578420623 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051389777/2500000000 : ℝ), (1561908743/5000000000 : ℝ), (2834989321/5000000000 : ℝ)] ![(15818031626911/50000000000000 : ℝ), (21310779893997/100000000000000 : ℝ), (23526578420623/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051389777/2500000000 : ℝ)|^8279 ≤ (15818031626911/50000000000000 : ℝ)^6231
        have hw : |(1051389777/2500000000 : ℝ)|=(1051389777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1561908743/5000000000 : ℝ)|^8279 ≤ (21310779893997/100000000000000 : ℝ)^6231
        have hw : |(1561908743/5000000000 : ℝ)|=(1561908743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2834989321/5000000000 : ℝ)|^8279 ≤ (23526578420623/50000000000000 : ℝ)^6231
        have hw : |(2834989321/5000000000 : ℝ)|=(2834989321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s0_4 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-382994987/2000000000 : ℝ)*x 0 + (2403377359/5000000000 : ℝ)*x 1 + (1508197013/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (382994987/2000000000 : ℝ)^8279 ≤ (5561539795521/50000000000000 : ℝ)^6231 := by
    have hnat : (382994987 : ℕ)^8279*50000000000000^6231 ≤ 5561539795521^6231*2000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      382994987 2000000000 5561539795521 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2403377359/5000000000 : ℝ)^8279 ≤ (37781859028813/100000000000000 : ℝ)^6231 := by
    have hnat : (2403377359 : ℕ)^8279*100000000000000^6231 ≤ 37781859028813^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2403377359 5000000000 37781859028813 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1508197013/2500000000 : ℝ)^8279 ≤ (51095061364759/100000000000000 : ℝ)^6231 := by
    have hnat : (1508197013 : ℕ)^8279*100000000000000^6231 ≤ 51095061364759^6231*2500000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1508197013 2500000000 51095061364759 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-382994987/2000000000 : ℝ), (2403377359/5000000000 : ℝ), (1508197013/2500000000 : ℝ)] ![(5561539795521/50000000000000 : ℝ), (37781859028813/100000000000000 : ℝ), (51095061364759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-382994987/2000000000 : ℝ)|^8279 ≤ (5561539795521/50000000000000 : ℝ)^6231
        have hw : |(-382994987/2000000000 : ℝ)|=(382994987/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2403377359/5000000000 : ℝ)|^8279 ≤ (37781859028813/100000000000000 : ℝ)^6231
        have hw : |(2403377359/5000000000 : ℝ)|=(2403377359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1508197013/2500000000 : ℝ)|^8279 ≤ (51095061364759/100000000000000 : ℝ)^6231
        have hw : |(1508197013/2500000000 : ℝ)|=(1508197013/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s0_5 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (64607789/125000000 : ℝ)*x 0 + (-1394476081/10000000000 : ℝ)*x 1 + (3016393389/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (64607789/125000000 : ℝ)^8279 ≤ (20803535813493/50000000000000 : ℝ)^6231 := by
    have hnat : (64607789 : ℕ)^8279*50000000000000^6231 ≤ 20803535813493^6231*125000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64607789 125000000 20803535813493 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1394476081/10000000000 : ℝ)^8279 ≤ (3648940665809/50000000000000 : ℝ)^6231 := by
    have hnat : (1394476081 : ℕ)^8279*50000000000000^6231 ≤ 3648940665809^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1394476081 10000000000 3648940665809 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3016393389/5000000000 : ℝ)^8279 ≤ (51095047028019/100000000000000 : ℝ)^6231 := by
    have hnat : (3016393389 : ℕ)^8279*100000000000000^6231 ≤ 51095047028019^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3016393389 5000000000 51095047028019 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(64607789/125000000 : ℝ), (-1394476081/10000000000 : ℝ), (3016393389/5000000000 : ℝ)] ![(20803535813493/50000000000000 : ℝ), (3648940665809/50000000000000 : ℝ), (51095047028019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(64607789/125000000 : ℝ)|^8279 ≤ (20803535813493/50000000000000 : ℝ)^6231
        have hw : |(64607789/125000000 : ℝ)|=(64607789/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1394476081/10000000000 : ℝ)|^8279 ≤ (3648940665809/50000000000000 : ℝ)^6231
        have hw : |(-1394476081/10000000000 : ℝ)|=(1394476081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3016393389/5000000000 : ℝ)|^8279 ≤ (51095047028019/100000000000000 : ℝ)^6231
        have hw : |(3016393389/5000000000 : ℝ)|=(3016393389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s0_6 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5168623301/10000000000 : ℝ)*x 0 + (1508196993/2500000000 : ℝ)*x 1 + (-1394473871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5168623301/10000000000 : ℝ)^8279 ≤ (20803536781461/50000000000000 : ℝ)^6231 := by
    have hnat : (5168623301 : ℕ)^8279*50000000000000^6231 ≤ 20803536781461^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5168623301 10000000000 20803536781461 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1508196993/2500000000 : ℝ)^8279 ≤ (12773765116123/25000000000000 : ℝ)^6231 := by
    have hnat : (1508196993 : ℕ)^8279*25000000000000^6231 ≤ 12773765116123^6231*2500000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1508196993 2500000000 12773765116123 25000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1394473871/10000000000 : ℝ)^8279 ≤ (3648932982151/50000000000000 : ℝ)^6231 := by
    have hnat : (1394473871 : ℕ)^8279*50000000000000^6231 ≤ 3648932982151^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1394473871 10000000000 3648932982151 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5168623301/10000000000 : ℝ), (1508196993/2500000000 : ℝ), (-1394473871/10000000000 : ℝ)] ![(20803536781461/50000000000000 : ℝ), (12773765116123/25000000000000 : ℝ), (3648932982151/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5168623301/10000000000 : ℝ)|^8279 ≤ (20803536781461/50000000000000 : ℝ)^6231
        have hw : |(5168623301/10000000000 : ℝ)|=(5168623301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1508196993/2500000000 : ℝ)|^8279 ≤ (12773765116123/25000000000000 : ℝ)^6231
        have hw : |(1508196993/2500000000 : ℝ)|=(1508196993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1394473871/10000000000 : ℝ)|^8279 ≤ (3648932982151/50000000000000 : ℝ)^6231
        have hw : |(-1394473871/10000000000 : ℝ)|=(1394473871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s0_7 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1054002679/2500000000 : ℝ)*x 0 + (5604247437/10000000000 : ℝ)*x 1 + (3191851671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054002679/2500000000 : ℝ)^8279 ≤ (15870284380293/50000000000000 : ℝ)^6231 := by
    have hnat : (1054002679 : ℕ)^8279*50000000000000^6231 ≤ 15870284380293^6231*2500000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054002679 2500000000 15870284380293 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5604247437/10000000000 : ℝ)^8279 ≤ (289561082161/625000000000 : ℝ)^6231 := by
    have hnat : (5604247437 : ℕ)^8279*625000000000^6231 ≤ 289561082161^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5604247437 10000000000 289561082161 625000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3191851671/10000000000 : ℝ)^8279 ≤ (2741207259593/12500000000000 : ℝ)^6231 := by
    have hnat : (3191851671 : ℕ)^8279*12500000000000^6231 ≤ 2741207259593^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3191851671 10000000000 2741207259593 12500000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1054002679/2500000000 : ℝ), (5604247437/10000000000 : ℝ), (3191851671/10000000000 : ℝ)] ![(15870284380293/50000000000000 : ℝ), (289561082161/625000000000 : ℝ), (2741207259593/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1054002679/2500000000 : ℝ)|^8279 ≤ (15870284380293/50000000000000 : ℝ)^6231
        have hw : |(1054002679/2500000000 : ℝ)|=(1054002679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5604247437/10000000000 : ℝ)|^8279 ≤ (289561082161/625000000000 : ℝ)^6231
        have hw : |(5604247437/10000000000 : ℝ)|=(5604247437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3191851671/10000000000 : ℝ)|^8279 ≤ (2741207259593/12500000000000 : ℝ)^6231
        have hw : |(3191851671/10000000000 : ℝ)|=(3191851671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1086_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74191131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (181/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (28031/100000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (4139/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4139 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4139*1^1024 ≤ 0^1024*1^4139 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4139 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4139/1024 : ℝ) ≤ (2463369692357564947/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4139 ≤ (2463369692357564947/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4139*100000000000000000000^1024 ≤ 2463369692357564947^1024*5^4139 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2463369692357564947 100000000000000000000 4139 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2463369692357564947/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4139/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4139 := by
      have hnat : (1 : ℕ)^1024*1^4139 ≤ 1^4139*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102463369692357564947/100000000000000000000 : ℝ) ≤ (10060387507062689/10000000000000000 : ℝ) ^ (4139/1024 : ℝ) := by
    have hpowers : (102463369692357564947/100000000000000000000 : ℝ)^1024 ≤ (10060387507062689/10000000000000000 : ℝ)^4139 := by
      have hnat : (102463369692357564947 : ℕ)^1024*10000000000000000^4139 ≤ 10060387507062689^4139*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102463369692357564947 100000000000000000000 10060387507062689 10000000000000000 1024 4139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10060387507062689/10000000000000000 : ℝ)) (X := (102463369692357564947/100000000000000000000 : ℝ)) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52463369692357564947/50000000000000000000 : ℝ) ≤ (5060387507062689/5000000000000000 : ℝ) ^ (4139/1024 : ℝ) := by
    have hpowers : (52463369692357564947/50000000000000000000 : ℝ)^1024 ≤ (5060387507062689/5000000000000000 : ℝ)^4139 := by
      have hnat : (52463369692357564947 : ℕ)^1024*5000000000000000^4139 ≤ 5060387507062689^4139*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52463369692357564947 50000000000000000000 5060387507062689 5000000000000000 1024 4139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5060387507062689/5000000000000000 : ℝ)) (X := (52463369692357564947/50000000000000000000 : ℝ)) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(60387507062689/4000000000000000 : ℝ)*(0 : ℝ))^(4139/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(60387507062689/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2463369692357564947/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(60387507062689/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4139/1024 : ℝ) := by
    rw [show (1 : ℝ)+(60387507062689/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10060387507062689/10000000000000000 : ℝ) by norm_num, show 1+(2463369692357564947/100000000000000000000 : ℝ)+(0 : ℝ)=(102463369692357564947/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2463369692357564947/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(60387507062689/4000000000000000 : ℝ)*(2/5 : ℝ))^(4139/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(60387507062689/4000000000000000 : ℝ)*(2/5 : ℝ)=(5060387507062689/5000000000000000 : ℝ) by norm_num, show 1+2*(2463369692357564947/100000000000000000000 : ℝ)=(52463369692357564947/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(60387507062689/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4139/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (60387507062689/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(60387507062689/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4139/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (60387507062689/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(60387507062689/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4139/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (60387507062689/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1909661637/10000000000 : ℝ)*X 0 0+(30336821/50000000 : ℝ)*X 0 1+(2386674611/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1103989493/2000000000 : ℝ)*X 1 0+(-2653912153/10000000000 : ℝ)*X 1 1+(2386674549/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((344996687/625000000 : ℝ)*X 2 0+(954669899/2000000000 : ℝ)*X 2 1+(-165869517/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1051389777/2500000000 : ℝ)*X 0 0+(1561908743/5000000000 : ℝ)*X 0 1+(2834989321/5000000000 : ℝ)*X 0 2+(1051389777/2500000000 : ℝ)*X 1 0+(1561908743/5000000000 : ℝ)*X 1 1+(2834989321/5000000000 : ℝ)*X 1 2+(1051389777/2500000000 : ℝ)*X 2 0+(1561908743/5000000000 : ℝ)*X 2 1+(2834989321/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-382994987/2000000000 : ℝ)*X 0 0+(2403377359/5000000000 : ℝ)*X 0 1+(1508197013/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((64607789/125000000 : ℝ)*X 1 0+(-1394476081/10000000000 : ℝ)*X 1 1+(3016393389/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5168623301/10000000000 : ℝ)*X 2 0+(1508196993/2500000000 : ℝ)*X 2 1+(-1394473871/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1054002679/2500000000 : ℝ)*X 0 0+(5604247437/10000000000 : ℝ)*X 0 1+(3191851671/10000000000 : ℝ)*X 0 2+(1054002679/2500000000 : ℝ)*X 1 0+(5604247437/10000000000 : ℝ)*X 1 1+(3191851671/10000000000 : ℝ)*X 1 2+(1054002679/2500000000 : ℝ)*X 2 0+(5604247437/10000000000 : ℝ)*X 2 1+(3191851671/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (312530670308680677138333/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (80123159/100000000000000 : ℝ)*(base1) + (8501351/1250000000000 : ℝ)*(base19) + (583877773/100000000000000 : ℝ)*(base23) + (3001043/10000000000000 : ℝ)*(base24) + (151203759/100000000000000 : ℝ)*(upper3) + (582770778420267/100000000000000 : ℝ)*(major0) + (582770778420267/100000000000000 : ℝ)*(major1) + (582770778420267/100000000000000 : ℝ)*(major2) + (193197666274939/25000000000000 : ℝ)*(sp0) + (193197786745889/25000000000000 : ℝ)*(sp1) + (772791213203433/100000000000000 : ℝ)*(sp2) + (7854972432279/2000000000000 : ℝ)*(sp3) + (1242115039/100000000000000 : ℝ)*(sp4) + (230958723/25000000000000 : ℝ)*(sp7) + (196374812786001/50000000000000 : ℝ)*(f.failure) + (193197956772909/25000000000000 : ℝ)*(f.sum) + (102482510117963/200000000000000000000000000000 : ℝ)*base65 + (3740196474717963/400000000000000000000000000000 : ℝ)*base67 + (2971227040317963/400000000000000000000000000000 : ℝ)*base69 + (2676554832317963/400000000000000000000000000000 : ℝ)*base71 + (300903669917963/200000000000000000000000000000 : ℝ)*base73 + (1727335589117963/400000000000000000000000000000 : ℝ)*base75 + (3343139633917963/400000000000000000000000000000 : ℝ)*base77 + (3241125621517963/400000000000000000000000000000 : ℝ)*base79 + (528466625917963/200000000000000000000000000000 : ℝ)*base81 + (157131/2500000000000000000000 : ℝ)*base89 + (157131/2500000000000000000000 : ℝ)*base91 + (157131/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (176211027347308800561897/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (82101837/20000000000000 : ℝ)*(base19) + (80586923/10000000000000 : ℝ)*(base23) + (321273483/100000000000000 : ℝ)*(base39) + (58945561/100000000000000 : ℝ)*(base45) + (8307651/100000000000000 : ℝ)*(upper2) + (137734937/50000000000000 : ℝ)*(upper5) + (153770306586509/25000000000000 : ℝ)*(major0) + (153770306586509/25000000000000 : ℝ)*(major1) + (615080905072553/100000000000000 : ℝ)*(major2) + (57132787/10000000000000 : ℝ)*(sp2) + (101954655824163/12500000000000 : ℝ)*(sp4) + (815636836084119/100000000000000 : ℝ)*(sp5) + (101954523833711/12500000000000 : ℝ)*(sp6) + (414524767351259/100000000000000 : ℝ)*(sp7) + (414524767351259/100000000000000 : ℝ)*(f.failure) + (203909391966697/25000000000000 : ℝ)*(f.sum) + (835478358674179/400000000000000000000000000000 : ℝ)*base66 + (353180882275017/400000000000000000000000000000 : ℝ)*base67 + (829341904962701/100000000000000000000000000000 : ℝ)*base69 + (893324374675017/400000000000000000000000000000 : ℝ)*base71 + (554982094674179/400000000000000000000000000000 : ℝ)*base74 + (396884427562701/100000000000000000000000000000 : ℝ)*base75 + (387263192537299/100000000000000000000000000000 : ℝ)*base78 + (398613507762701/100000000000000000000000000000 : ℝ)*base79 + (22754619612701/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (20516071/5000000000000000000000 : ℝ)*base90 + (20516071/5000000000000000000000 : ℝ)*base92 + (20516071/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1086_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74191131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (181/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (28031/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1086_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1086_s1_0 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2118363381/10000000000 : ℝ)*x 0 + (5716737453/10000000000 : ℝ)*x 1 + (4990336167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2118363381/10000000000 : ℝ)^8279 ≤ (6359761738291/50000000000000 : ℝ)^6231 := by
    have hnat : (2118363381 : ℕ)^8279*50000000000000^6231 ≤ 6359761738291^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118363381 10000000000 6359761738291 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5716737453/10000000000 : ℝ)^8279 ≤ (951388564141/2000000000000 : ℝ)^6231 := by
    have hnat : (5716737453 : ℕ)^8279*2000000000000^6231 ≤ 951388564141^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5716737453 10000000000 951388564141 2000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4990336167/10000000000 : ℝ)^8279 ≤ (39711048295717/100000000000000 : ℝ)^6231 := by
    have hnat : (4990336167 : ℕ)^8279*100000000000000^6231 ≤ 39711048295717^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4990336167 10000000000 39711048295717 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2118363381/10000000000 : ℝ), (5716737453/10000000000 : ℝ), (4990336167/10000000000 : ℝ)] ![(6359761738291/50000000000000 : ℝ), (951388564141/2000000000000 : ℝ), (39711048295717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2118363381/10000000000 : ℝ)|^8279 ≤ (6359761738291/50000000000000 : ℝ)^6231
        have hw : |(-2118363381/10000000000 : ℝ)|=(2118363381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5716737453/10000000000 : ℝ)|^8279 ≤ (951388564141/2000000000000 : ℝ)^6231
        have hw : |(5716737453/10000000000 : ℝ)|=(5716737453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4990336167/10000000000 : ℝ)|^8279 ≤ (39711048295717/100000000000000 : ℝ)^6231
        have hw : |(4990336167/10000000000 : ℝ)|=(4990336167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s1_1 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2711102789/5000000000 : ℝ)*x 0 + (-627877217/2500000000 : ℝ)*x 1 + (4990336413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2711102789/5000000000 : ℝ)^8279 ≤ (44340966692107/100000000000000 : ℝ)^6231 := by
    have hnat : (2711102789 : ℕ)^8279*100000000000000^6231 ≤ 44340966692107^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711102789 5000000000 44340966692107 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (627877217/2500000000 : ℝ)^8279 ≤ (3986995599307/25000000000000 : ℝ)^6231 := by
    have hnat : (627877217 : ℕ)^8279*25000000000000^6231 ≤ 3986995599307^6231*2500000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627877217 2500000000 3986995599307 25000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4990336413/10000000000 : ℝ)^8279 ≤ (4963881362087/12500000000000 : ℝ)^6231 := by
    have hnat : (4990336413 : ℕ)^8279*12500000000000^6231 ≤ 4963881362087^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4990336413 10000000000 4963881362087 12500000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2711102789/5000000000 : ℝ), (-627877217/2500000000 : ℝ), (4990336413/10000000000 : ℝ)] ![(44340966692107/100000000000000 : ℝ), (3986995599307/25000000000000 : ℝ), (4963881362087/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2711102789/5000000000 : ℝ)|^8279 ≤ (44340966692107/100000000000000 : ℝ)^6231
        have hw : |(2711102789/5000000000 : ℝ)|=(2711102789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-627877217/2500000000 : ℝ)|^8279 ≤ (3986995599307/25000000000000 : ℝ)^6231
        have hw : |(-627877217/2500000000 : ℝ)|=(627877217/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4990336413/10000000000 : ℝ)|^8279 ≤ (4963881362087/12500000000000 : ℝ)^6231
        have hw : |(4990336413/10000000000 : ℝ)|=(4990336413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s1_2 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (542220641/1000000000 : ℝ)*x 0 + (2495167773/5000000000 : ℝ)*x 1 + (-2511508883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542220641/1000000000 : ℝ)^8279 ≤ (22170487866097/50000000000000 : ℝ)^6231 := by
    have hnat : (542220641 : ℕ)^8279*50000000000000^6231 ≤ 22170487866097^6231*1000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542220641 1000000000 22170487866097 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2495167773/5000000000 : ℝ)^8279 ≤ (4963880216229/12500000000000 : ℝ)^6231 := by
    have hnat : (2495167773 : ℕ)^8279*12500000000000^6231 ≤ 4963880216229^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2495167773 5000000000 4963880216229 12500000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2511508883/10000000000 : ℝ)^8279 ≤ (1993497815473/12500000000000 : ℝ)^6231 := by
    have hnat : (2511508883 : ℕ)^8279*12500000000000^6231 ≤ 1993497815473^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2511508883 10000000000 1993497815473 12500000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(542220641/1000000000 : ℝ), (2495167773/5000000000 : ℝ), (-2511508883/10000000000 : ℝ)] ![(22170487866097/50000000000000 : ℝ), (4963880216229/12500000000000 : ℝ), (1993497815473/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(542220641/1000000000 : ℝ)|^8279 ≤ (22170487866097/50000000000000 : ℝ)^6231
        have hw : |(542220641/1000000000 : ℝ)|=(542220641/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2495167773/5000000000 : ℝ)|^8279 ≤ (4963880216229/12500000000000 : ℝ)^6231
        have hw : |(2495167773/5000000000 : ℝ)|=(2495167773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2511508883/10000000000 : ℝ)|^8279 ≤ (1993497815473/12500000000000 : ℝ)^6231
        have hw : |(-2511508883/10000000000 : ℝ)|=(2511508883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s1_3 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4322144371/10000000000 : ℝ)*x 0 + (3666415017/10000000000 : ℝ)*x 1 + (2547856793/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4322144371/10000000000 : ℝ)^8279 ≤ (6561319679507/20000000000000 : ℝ)^6231 := by
    have hnat : (4322144371 : ℕ)^8279*20000000000000^6231 ≤ 6561319679507^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4322144371 10000000000 6561319679507 20000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3666415017/10000000000 : ℝ)^8279 ≤ (26364340680083/100000000000000 : ℝ)^6231 := by
    have hnat : (3666415017 : ℕ)^8279*100000000000000^6231 ≤ 26364340680083^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3666415017 10000000000 26364340680083 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2547856793/5000000000 : ℝ)^8279 ≤ (40829060905143/100000000000000 : ℝ)^6231 := by
    have hnat : (2547856793 : ℕ)^8279*100000000000000^6231 ≤ 40829060905143^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2547856793 5000000000 40829060905143 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4322144371/10000000000 : ℝ), (3666415017/10000000000 : ℝ), (2547856793/5000000000 : ℝ)] ![(6561319679507/20000000000000 : ℝ), (26364340680083/100000000000000 : ℝ), (40829060905143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4322144371/10000000000 : ℝ)|^8279 ≤ (6561319679507/20000000000000 : ℝ)^6231
        have hw : |(4322144371/10000000000 : ℝ)|=(4322144371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3666415017/10000000000 : ℝ)|^8279 ≤ (26364340680083/100000000000000 : ℝ)^6231
        have hw : |(3666415017/10000000000 : ℝ)|=(3666415017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2547856793/5000000000 : ℝ)|^8279 ≤ (40829060905143/100000000000000 : ℝ)^6231
        have hw : |(2547856793/5000000000 : ℝ)|=(2547856793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s1_4 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2119251179/10000000000 : ℝ)*x 0 + (625058523/1250000000 : ℝ)*x 1 + (5706401059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2119251179/10000000000 : ℝ)^8279 ≤ (12726606759397/100000000000000 : ℝ)^6231 := by
    have hnat : (2119251179 : ℕ)^8279*100000000000000^6231 ≤ 12726606759397^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119251179 10000000000 12726606759397 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (625058523/1250000000 : ℝ)^8279 ≤ (19909105345063/50000000000000 : ℝ)^6231 := by
    have hnat : (625058523 : ℕ)^8279*50000000000000^6231 ≤ 19909105345063^6231*1250000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      625058523 1250000000 19909105345063 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5706401059/10000000000 : ℝ)^8279 ≤ (47455182536181/100000000000000 : ℝ)^6231 := by
    have hnat : (5706401059 : ℕ)^8279*100000000000000^6231 ≤ 47455182536181^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5706401059 10000000000 47455182536181 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2119251179/10000000000 : ℝ), (625058523/1250000000 : ℝ), (5706401059/10000000000 : ℝ)] ![(12726606759397/100000000000000 : ℝ), (19909105345063/50000000000000 : ℝ), (47455182536181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2119251179/10000000000 : ℝ)|^8279 ≤ (12726606759397/100000000000000 : ℝ)^6231
        have hw : |(-2119251179/10000000000 : ℝ)|=(2119251179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(625058523/1250000000 : ℝ)|^8279 ≤ (19909105345063/50000000000000 : ℝ)^6231
        have hw : |(625058523/1250000000 : ℝ)|=(625058523/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5706401059/10000000000 : ℝ)|^8279 ≤ (47455182536181/100000000000000 : ℝ)^6231
        have hw : |(5706401059/10000000000 : ℝ)|=(5706401059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s1_5 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (65456251/125000000 : ℝ)*x 0 + (-897721929/5000000000 : ℝ)*x 1 + (1141280231/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65456251/125000000 : ℝ)^8279 ≤ (42334630842369/100000000000000 : ℝ)^6231 := by
    have hnat : (65456251 : ℕ)^8279*100000000000000^6231 ≤ 42334630842369^6231*125000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65456251 125000000 42334630842369 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (897721929/5000000000 : ℝ)^8279 ≤ (10210185551879/100000000000000 : ℝ)^6231 := by
    have hnat : (897721929 : ℕ)^8279*100000000000000^6231 ≤ 10210185551879^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897721929 5000000000 10210185551879 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1141280231/2000000000 : ℝ)^8279 ≤ (4745518359693/10000000000000 : ℝ)^6231 := by
    have hnat : (1141280231 : ℕ)^8279*10000000000000^6231 ≤ 4745518359693^6231*2000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141280231 2000000000 4745518359693 10000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(65456251/125000000 : ℝ), (-897721929/5000000000 : ℝ), (1141280231/2000000000 : ℝ)] ![(42334630842369/100000000000000 : ℝ), (10210185551879/100000000000000 : ℝ), (4745518359693/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(65456251/125000000 : ℝ)|^8279 ≤ (42334630842369/100000000000000 : ℝ)^6231
        have hw : |(65456251/125000000 : ℝ)|=(65456251/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-897721929/5000000000 : ℝ)|^8279 ≤ (10210185551879/100000000000000 : ℝ)^6231
        have hw : |(-897721929/5000000000 : ℝ)|=(897721929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1141280231/2000000000 : ℝ)|^8279 ≤ (4745518359693/10000000000000 : ℝ)^6231
        have hw : |(1141280231/2000000000 : ℝ)|=(1141280231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s1_6 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5236499923/10000000000 : ℝ)*x 0 + (5706401099/10000000000 : ℝ)*x 1 + (-1795444163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5236499923/10000000000 : ℝ)^8279 ≤ (8466925831183/20000000000000 : ℝ)^6231 := by
    have hnat : (5236499923 : ℕ)^8279*20000000000000^6231 ≤ 8466925831183^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236499923 10000000000 8466925831183 20000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5706401099/10000000000 : ℝ)^8279 ≤ (593189787227/1250000000000 : ℝ)^6231 := by
    have hnat : (5706401099 : ℕ)^8279*1250000000000^6231 ≤ 593189787227^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5706401099 10000000000 593189787227 1250000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1795444163/10000000000 : ℝ)^8279 ≤ (5105093928203/50000000000000 : ℝ)^6231 := by
    have hnat : (1795444163 : ℕ)^8279*50000000000000^6231 ≤ 5105093928203^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1795444163 10000000000 5105093928203 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5236499923/10000000000 : ℝ), (5706401099/10000000000 : ℝ), (-1795444163/10000000000 : ℝ)] ![(8466925831183/20000000000000 : ℝ), (593189787227/1250000000000 : ℝ), (5105093928203/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5236499923/10000000000 : ℝ)|^8279 ≤ (8466925831183/20000000000000 : ℝ)^6231
        have hw : |(5236499923/10000000000 : ℝ)|=(5236499923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5706401099/10000000000 : ℝ)|^8279 ≤ (593189787227/1250000000000 : ℝ)^6231
        have hw : |(5706401099/10000000000 : ℝ)|=(5706401099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1795444163/10000000000 : ℝ)|^8279 ≤ (5105093928203/50000000000000 : ℝ)^6231
        have hw : |(-1795444163/10000000000 : ℝ)|=(1795444163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s1_7 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2161945137/5000000000 : ℝ)*x 0 + (5075777797/10000000000 : ℝ)*x 1 + (737350589/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2161945137/5000000000 : ℝ)^8279 ≤ (32824207247863/100000000000000 : ℝ)^6231 := by
    have hnat : (2161945137 : ℕ)^8279*100000000000000^6231 ≤ 32824207247863^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161945137 5000000000 32824207247863 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5075777797/10000000000 : ℝ)^8279 ≤ (20308481011193/50000000000000 : ℝ)^6231 := by
    have hnat : (5075777797 : ℕ)^8279*50000000000000^6231 ≤ 20308481011193^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5075777797 10000000000 20308481011193 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (737350589/2000000000 : ℝ)^8279 ≤ (26558830719411/100000000000000 : ℝ)^6231 := by
    have hnat : (737350589 : ℕ)^8279*100000000000000^6231 ≤ 26558830719411^6231*2000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      737350589 2000000000 26558830719411 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2161945137/5000000000 : ℝ), (5075777797/10000000000 : ℝ), (737350589/2000000000 : ℝ)] ![(32824207247863/100000000000000 : ℝ), (20308481011193/50000000000000 : ℝ), (26558830719411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2161945137/5000000000 : ℝ)|^8279 ≤ (32824207247863/100000000000000 : ℝ)^6231
        have hw : |(2161945137/5000000000 : ℝ)|=(2161945137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5075777797/10000000000 : ℝ)|^8279 ≤ (20308481011193/50000000000000 : ℝ)^6231
        have hw : |(5075777797/10000000000 : ℝ)|=(5075777797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(737350589/2000000000 : ℝ)|^8279 ≤ (26558830719411/100000000000000 : ℝ)^6231
        have hw : |(737350589/2000000000 : ℝ)|=(737350589/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1086_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74191131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28031/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (181/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (533/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2587/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (28031/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (181/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (28031/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (181/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (28031/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (181/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (28031/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (181/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (28031/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (181/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (28031/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (181/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (181/100000 : ℝ) ^ (4139/1024 : ℝ) ≤ (411650103/50000000000000000000 : ℝ) := by
    have hpowers : (181/100000 : ℝ)^4139 ≤ (411650103/50000000000000000000 : ℝ)^1024 := by
      have hnat : (181 : ℕ)^4139*50000000000000000000^1024 ≤ 411650103^1024*100000^4139 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        181 100000 411650103 50000000000000000000 4139 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (181/100000 : ℝ)) (X := (411650103/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (28031/100000 : ℝ) ^ (4139/1024 : ℝ) ≤ (292637182041207031/50000000000000000000 : ℝ) := by
    have hpowers : (28031/100000 : ℝ)^4139 ≤ (292637182041207031/50000000000000000000 : ℝ)^1024 := by
      have hnat : (28031 : ℕ)^4139*50000000000000000000^1024 ≤ 292637182041207031^1024*100000^4139 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28031 100000 292637182041207031 50000000000000000000 4139 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (28031/100000 : ℝ)) (X := (292637182041207031/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000000411650103/25000000000000000000 : ℝ) ≤ (5000000000020369/5000000000000000 : ℝ) ^ (4139/1024 : ℝ) := by
    have hpowers : (25000000000411650103/25000000000000000000 : ℝ)^1024 ≤ (5000000000020369/5000000000000000 : ℝ)^4139 := by
      have hnat : (25000000000411650103 : ℕ)^1024*5000000000000000^4139 ≤ 5000000000020369^4139*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000000411650103 25000000000000000000 5000000000020369 5000000000000000 1024 4139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000000020369/5000000000000000 : ℝ)) (X := (25000000000411650103/25000000000000000000 : ℝ)) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25146318591226428567/25000000000000000000 : ℝ) ≤ (10014448067468871/10000000000000000 : ℝ) ^ (4139/1024 : ℝ) := by
    have hpowers : (25146318591226428567/25000000000000000000 : ℝ)^1024 ≤ (10014448067468871/10000000000000000 : ℝ)^4139 := by
      have hnat : (25146318591226428567 : ℕ)^1024*10000000000000000^4139 ≤ 10014448067468871^4139*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25146318591226428567 25000000000000000000 10014448067468871 10000000000000000 1024 4139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10014448067468871/10000000000000000 : ℝ)) (X := (25146318591226428567/25000000000000000000 : ℝ)) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25292637182041207031/25000000000000000000 : ℝ) ≤ (2507224033724251/2500000000000000 : ℝ) ^ (4139/1024 : ℝ) := by
    have hpowers : (25292637182041207031/25000000000000000000 : ℝ)^1024 ≤ (2507224033724251/2500000000000000 : ℝ)^4139 := by
      have hnat : (25292637182041207031 : ℕ)^1024*2500000000000000^4139 ≤ 2507224033724251^4139*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25292637182041207031 25000000000000000000 2507224033724251 2500000000000000 1024 4139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2507224033724251/2500000000000000 : ℝ)) (X := (25292637182041207031/25000000000000000000 : ℝ)) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(411650103/50000000000000000000 : ℝ) ≤ ((139247384900362784577/139250000000000000000 : ℝ)+2*(14448067428133/2785000000000000 : ℝ)*(181/100000 : ℝ))^(4139/1024 : ℝ) := by
    rw [show (139247384900362784577/139250000000000000000 : ℝ)+2*(14448067428133/2785000000000000 : ℝ)*(181/100000 : ℝ)=(5000000000020369/5000000000000000 : ℝ) by norm_num, show 1+2*(411650103/50000000000000000000 : ℝ)=(25000000000411650103/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(292637182041207031/50000000000000000000 : ℝ)+(411650103/50000000000000000000 : ℝ) ≤ ((139247384900362784577/139250000000000000000 : ℝ)+(14448067428133/2785000000000000 : ℝ)*((28031/100000 : ℝ)+(181/100000 : ℝ)))^(4139/1024 : ℝ) := by
    rw [show (139247384900362784577/139250000000000000000 : ℝ)+(14448067428133/2785000000000000 : ℝ)*((28031/100000 : ℝ)+(181/100000 : ℝ))=(10014448067468871/10000000000000000 : ℝ) by norm_num, show 1+(292637182041207031/50000000000000000000 : ℝ)+(411650103/50000000000000000000 : ℝ)=(25146318591226428567/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(292637182041207031/50000000000000000000 : ℝ) ≤ ((139247384900362784577/139250000000000000000 : ℝ)+2*(14448067428133/2785000000000000 : ℝ)*(28031/100000 : ℝ))^(4139/1024 : ℝ) := by
    rw [show (139247384900362784577/139250000000000000000 : ℝ)+2*(14448067428133/2785000000000000 : ℝ)*(28031/100000 : ℝ)=(2507224033724251/2500000000000000 : ℝ) by norm_num, show 1+2*(292637182041207031/50000000000000000000 : ℝ)=(25292637182041207031/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (139247384900362784577/139250000000000000000 : ℝ)*(X 1 0+X 2 0)+(14448067428133/2785000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4139/1024 : ℝ)) (lo := (181/100000 : ℝ)) (hi := (28031/100000 : ℝ)) (c := (139247384900362784577/139250000000000000000 : ℝ)) (alpha := (14448067428133/2785000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (139247384900362784577/139250000000000000000 : ℝ)*(X 0 1+X 2 1)+(14448067428133/2785000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4139/1024 : ℝ)) (lo := (181/100000 : ℝ)) (hi := (28031/100000 : ℝ)) (c := (139247384900362784577/139250000000000000000 : ℝ)) (alpha := (14448067428133/2785000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (139247384900362784577/139250000000000000000 : ℝ)*(X 0 2+X 1 2)+(14448067428133/2785000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4139/1024 : ℝ)) (lo := (181/100000 : ℝ)) (hi := (28031/100000 : ℝ)) (c := (139247384900362784577/139250000000000000000 : ℝ)) (alpha := (14448067428133/2785000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2118363381/10000000000 : ℝ)*X 0 0+(5716737453/10000000000 : ℝ)*X 0 1+(4990336167/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2711102789/5000000000 : ℝ)*X 1 0+(-627877217/2500000000 : ℝ)*X 1 1+(4990336413/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((542220641/1000000000 : ℝ)*X 2 0+(2495167773/5000000000 : ℝ)*X 2 1+(-2511508883/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4322144371/10000000000 : ℝ)*X 0 0+(3666415017/10000000000 : ℝ)*X 0 1+(2547856793/5000000000 : ℝ)*X 0 2+(4322144371/10000000000 : ℝ)*X 1 0+(3666415017/10000000000 : ℝ)*X 1 1+(2547856793/5000000000 : ℝ)*X 1 2+(4322144371/10000000000 : ℝ)*X 2 0+(3666415017/10000000000 : ℝ)*X 2 1+(2547856793/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2119251179/10000000000 : ℝ)*X 0 0+(625058523/1250000000 : ℝ)*X 0 1+(5706401059/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((65456251/125000000 : ℝ)*X 1 0+(-897721929/5000000000 : ℝ)*X 1 1+(1141280231/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5236499923/10000000000 : ℝ)*X 2 0+(5706401099/10000000000 : ℝ)*X 2 1+(-1795444163/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2161945137/5000000000 : ℝ)*X 0 0+(5075777797/10000000000 : ℝ)*X 0 1+(737350589/2000000000 : ℝ)*X 0 2+(2161945137/5000000000 : ℝ)*X 1 0+(5075777797/10000000000 : ℝ)*X 1 1+(737350589/2000000000 : ℝ)*X 1 2+(2161945137/5000000000 : ℝ)*X 2 0+(5075777797/10000000000 : ℝ)*X 2 1+(737350589/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (52339094822111139119719235241/6962500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (166385131/100000000000000 : ℝ)*(base1) + (1553988431/100000000000000 : ℝ)*(base19) + (1765227859/100000000000000 : ℝ)*(base23) + (6912379/5000000000000 : ℝ)*(upper3) + (190291017/100000000000000 : ℝ)*(upper5) + (1038158012641789/100000000000000 : ℝ)*(major0) + (1038158012641789/100000000000000 : ℝ)*(major1) + (1038158012641789/100000000000000 : ℝ)*(major2) + (688328332218047/50000000000000 : ℝ)*(sp0) + (172082899832117/12500000000000 : ℝ)*(sp1) + (344165746854377/25000000000000 : ℝ)*(sp2) + (43727957686659/6250000000000 : ℝ)*(sp3) + (2063648601/25000000000000 : ℝ)*(sp4) + (1766345187/50000000000000 : ℝ)*(sp7) + (13993020441241/2000000000000 : ℝ)*(f.failure) + (1376664752645367/100000000000000 : ℝ)*(f.sum) + (70574323877437/139250000000000000000000000000 : ℝ)*base65 + (49256574716871738253/13925000000000000000000000000000000 : ℝ)*base67 + (40027677676328261747/13925000000000000000000000000000000 : ℝ)*base70 + (17516945350671738253/13925000000000000000000000000000000 : ℝ)*base71 + (360303623788437/139250000000000000000000000000 : ℝ)*base73 + (29811253774778261747/13925000000000000000000000000000000 : ℝ)*base76 + (7264841338071738253/13925000000000000000000000000000000 : ℝ)*base77 + (46556956550621738253/13925000000000000000000000000000000 : ℝ)*base79 + (491943384962563/139250000000000000000000000000 : ℝ)*base82 + (166429/100000000000000000000 : ℝ)*base90 + (166429/100000000000000000000 : ℝ)*base92 + (166429/100000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5137557488880931446645926817/696250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29617679/50000000000000 : ℝ)*(base1) + (790149009/50000000000000 : ℝ)*(base19) + (1508997943/100000000000000 : ℝ)*(base23) + (4005837/2500000000000 : ℝ)*(upper3) + (190623101/100000000000000 : ℝ)*(upper5) + (213649499755293/20000000000000 : ℝ)*(major0) + (213649499755293/20000000000000 : ℝ)*(major1) + (213649499755293/20000000000000 : ℝ)*(major2) + (6955796331/100000000000000 : ℝ)*(sp1) + (6142851129/100000000000000 : ℝ)*(sp2) + (708282715436139/50000000000000 : ℝ)*(sp4) + (1416556835542571/100000000000000 : ℝ)*(sp5) + (1416557719787847/100000000000000 : ℝ)*(sp6) + (44995582544837/6250000000000 : ℝ)*(sp7) + (2879717519811/400000000000 : ℝ)*(f.failure) + (35414134290923/2500000000000 : ℝ)*(f.sum) + (39117763216869/27850000000000000000000000000 : ℝ)*base65 + (9816857905687033939/2785000000000000000000000000000000 : ℝ)*base68 + (22531994148502966061/2785000000000000000000000000000000 : ℝ)*base69 + (9420427022762966061/2785000000000000000000000000000000 : ℝ)*base71 + (130655100206331/27850000000000000000000000000 : ℝ)*base74 + (6562169708792966061/2785000000000000000000000000000000 : ℝ)*base75 + (13691690528457966061/2785000000000000000000000000000000 : ℝ)*base77 + (19436859698337966061/2785000000000000000000000000000000 : ℝ)*base79 + (102542689662769/27850000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (3759/20000000000000000000 : ℝ)*base90 + (3759/20000000000000000000 : ℝ)*base92 + (3759/20000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1086_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74191131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28031/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (181/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (533/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2587/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1086_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1086_s2_0 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2174659833/10000000000 : ℝ)*x 0 + (5521806939/10000000000 : ℝ)*x 1 + (643691007/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174659833/10000000000 : ℝ)^8279 ≤ (13170602920401/100000000000000 : ℝ)^6231 := by
    have hnat : (2174659833 : ℕ)^8279*100000000000000^6231 ≤ 13170602920401^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174659833 10000000000 13170602920401 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5521806939/10000000000 : ℝ)^8279 ≤ (45426437915539/100000000000000 : ℝ)^6231 := by
    have hnat : (5521806939 : ℕ)^8279*100000000000000^6231 ≤ 45426437915539^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5521806939 10000000000 45426437915539 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (643691007/1250000000 : ℝ)^8279 ≤ (10350739786873/25000000000000 : ℝ)^6231 := by
    have hnat : (643691007 : ℕ)^8279*25000000000000^6231 ≤ 10350739786873^6231*1250000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643691007 1250000000 10350739786873 25000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2174659833/10000000000 : ℝ), (5521806939/10000000000 : ℝ), (643691007/1250000000 : ℝ)] ![(13170602920401/100000000000000 : ℝ), (45426437915539/100000000000000 : ℝ), (10350739786873/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2174659833/10000000000 : ℝ)|^8279 ≤ (13170602920401/100000000000000 : ℝ)^6231
        have hw : |(-2174659833/10000000000 : ℝ)|=(2174659833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5521806939/10000000000 : ℝ)|^8279 ≤ (45426437915539/100000000000000 : ℝ)^6231
        have hw : |(5521806939/10000000000 : ℝ)|=(5521806939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(643691007/1250000000 : ℝ)|^8279 ≤ (10350739786873/25000000000000 : ℝ)^6231
        have hw : |(643691007/1250000000 : ℝ)|=(643691007/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s2_1 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1344077539/2500000000 : ℝ)*x 0 + (-148040337/625000000 : ℝ)*x 1 + (5149528617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344077539/2500000000 : ℝ)^8279 ≤ (219214927213/500000000000 : ℝ)^6231 := by
    have hnat : (1344077539 : ℕ)^8279*500000000000^6231 ≤ 219214927213^6231*2500000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344077539 2500000000 219214927213 500000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (148040337/625000000 : ℝ)^8279 ≤ (14754049403573/100000000000000 : ℝ)^6231 := by
    have hnat : (148040337 : ℕ)^8279*100000000000000^6231 ≤ 14754049403573^6231*625000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      148040337 625000000 14754049403573 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5149528617/10000000000 : ℝ)^8279 ≤ (41402965140529/100000000000000 : ℝ)^6231 := by
    have hnat : (5149528617 : ℕ)^8279*100000000000000^6231 ≤ 41402965140529^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5149528617 10000000000 41402965140529 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344077539/2500000000 : ℝ), (-148040337/625000000 : ℝ), (5149528617/10000000000 : ℝ)] ![(219214927213/500000000000 : ℝ), (14754049403573/100000000000000 : ℝ), (41402965140529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344077539/2500000000 : ℝ)|^8279 ≤ (219214927213/500000000000 : ℝ)^6231
        have hw : |(1344077539/2500000000 : ℝ)|=(1344077539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-148040337/625000000 : ℝ)|^8279 ≤ (14754049403573/100000000000000 : ℝ)^6231
        have hw : |(-148040337/625000000 : ℝ)|=(148040337/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5149528617/10000000000 : ℝ)|^8279 ≤ (41402965140529/100000000000000 : ℝ)^6231
        have hw : |(5149528617/10000000000 : ℝ)|=(5149528617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s2_2 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5376310291/10000000000 : ℝ)*x 0 + (321845529/625000000 : ℝ)*x 1 + (-2368645413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376310291/10000000000 : ℝ)^8279 ≤ (10960746726337/25000000000000 : ℝ)^6231 := by
    have hnat : (5376310291 : ℕ)^8279*25000000000000^6231 ≤ 10960746726337^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376310291 10000000000 10960746726337 25000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (321845529/625000000 : ℝ)^8279 ≤ (2587685219129/6250000000000 : ℝ)^6231 := by
    have hnat : (321845529 : ℕ)^8279*6250000000000^6231 ≤ 2587685219129^6231*625000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321845529 625000000 2587685219129 6250000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2368645413/10000000000 : ℝ)^8279 ≤ (14754049577373/100000000000000 : ℝ)^6231 := by
    have hnat : (2368645413 : ℕ)^8279*100000000000000^6231 ≤ 14754049577373^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2368645413 10000000000 14754049577373 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376310291/10000000000 : ℝ), (321845529/625000000 : ℝ), (-2368645413/10000000000 : ℝ)] ![(10960746726337/25000000000000 : ℝ), (2587685219129/6250000000000 : ℝ), (14754049577373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376310291/10000000000 : ℝ)|^8279 ≤ (10960746726337/25000000000000 : ℝ)^6231
        have hw : |(5376310291/10000000000 : ℝ)|=(5376310291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(321845529/625000000 : ℝ)|^8279 ≤ (2587685219129/6250000000000 : ℝ)^6231
        have hw : |(321845529/625000000 : ℝ)|=(321845529/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2368645413/10000000000 : ℝ)|^8279 ≤ (14754049577373/100000000000000 : ℝ)^6231
        have hw : |(-2368645413/10000000000 : ℝ)|=(2368645413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s2_3 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4360613563/10000000000 : ℝ)*x 0 + (4009797383/10000000000 : ℝ)*x 1 + (237115447/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360613563/10000000000 : ℝ)^8279 ≤ (3319513205787/10000000000000 : ℝ)^6231 := by
    have hnat : (4360613563 : ℕ)^8279*10000000000000^6231 ≤ 3319513205787^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360613563 10000000000 3319513205787 10000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4009797383/10000000000 : ℝ)^8279 ≤ (1484728467669/5000000000000 : ℝ)^6231 := by
    have hnat : (4009797383 : ℕ)^8279*5000000000000^6231 ≤ 1484728467669^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4009797383 10000000000 1484728467669 5000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (237115447/500000000 : ℝ)^8279 ≤ (18555149290857/50000000000000 : ℝ)^6231 := by
    have hnat : (237115447 : ℕ)^8279*50000000000000^6231 ≤ 18555149290857^6231*500000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237115447 500000000 18555149290857 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360613563/10000000000 : ℝ), (4009797383/10000000000 : ℝ), (237115447/500000000 : ℝ)] ![(3319513205787/10000000000000 : ℝ), (1484728467669/5000000000000 : ℝ), (18555149290857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360613563/10000000000 : ℝ)|^8279 ≤ (3319513205787/10000000000000 : ℝ)^6231
        have hw : |(4360613563/10000000000 : ℝ)|=(4360613563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4009797383/10000000000 : ℝ)|^8279 ≤ (1484728467669/5000000000000 : ℝ)^6231
        have hw : |(4009797383/10000000000 : ℝ)|=(4009797383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(237115447/500000000 : ℝ)|^8279 ≤ (18555149290857/50000000000000 : ℝ)^6231
        have hw : |(237115447/500000000 : ℝ)|=(237115447/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s2_4 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1087389571/5000000000 : ℝ)*x 0 + (1288049537/2500000000 : ℝ)*x 1 + (5519109133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087389571/5000000000 : ℝ)^8279 ≤ (6585781504791/50000000000000 : ℝ)^6231 := by
    have hnat : (1087389571 : ℕ)^8279*50000000000000^6231 ≤ 6585781504791^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087389571 5000000000 6585781504791 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1288049537/2500000000 : ℝ)^8279 ≤ (10357871392521/25000000000000 : ℝ)^6231 := by
    have hnat : (1288049537 : ℕ)^8279*25000000000000^6231 ≤ 10357871392521^6231*2500000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1288049537 2500000000 10357871392521 25000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5519109133/10000000000 : ℝ)^8279 ≤ (22698475700589/50000000000000 : ℝ)^6231 := by
    have hnat : (5519109133 : ℕ)^8279*50000000000000^6231 ≤ 22698475700589^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5519109133 10000000000 22698475700589 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1087389571/5000000000 : ℝ), (1288049537/2500000000 : ℝ), (5519109133/10000000000 : ℝ)] ![(6585781504791/50000000000000 : ℝ), (10357871392521/25000000000000 : ℝ), (22698475700589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1087389571/5000000000 : ℝ)|^8279 ≤ (6585781504791/50000000000000 : ℝ)^6231
        have hw : |(-1087389571/5000000000 : ℝ)|=(1087389571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1288049537/2500000000 : ℝ)|^8279 ≤ (10357871392521/25000000000000 : ℝ)^6231
        have hw : |(1288049537/2500000000 : ℝ)|=(1288049537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5519109133/10000000000 : ℝ)|^8279 ≤ (22698475700589/50000000000000 : ℝ)^6231
        have hw : |(5519109133/10000000000 : ℝ)|=(5519109133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s2_5 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (660276487/1250000000 : ℝ)*x 0 + (-1999064767/10000000000 : ℝ)*x 1 + (220764369/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660276487/1250000000 : ℝ)^8279 ≤ (8565271702779/20000000000000 : ℝ)^6231 := by
    have hnat : (660276487 : ℕ)^8279*20000000000000^6231 ≤ 8565271702779^6231*1250000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660276487 1250000000 8565271702779 20000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1999064767/10000000000 : ℝ)^8279 ≤ (2944172267387/25000000000000 : ℝ)^6231 := by
    have hnat : (1999064767 : ℕ)^8279*25000000000000^6231 ≤ 2944172267387^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1999064767 10000000000 2944172267387 25000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (220764369/400000000 : ℝ)^8279 ≤ (567461905083/1250000000000 : ℝ)^6231 := by
    have hnat : (220764369 : ℕ)^8279*1250000000000^6231 ≤ 567461905083^6231*400000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220764369 400000000 567461905083 1250000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660276487/1250000000 : ℝ), (-1999064767/10000000000 : ℝ), (220764369/400000000 : ℝ)] ![(8565271702779/20000000000000 : ℝ), (2944172267387/25000000000000 : ℝ), (567461905083/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660276487/1250000000 : ℝ)|^8279 ≤ (8565271702779/20000000000000 : ℝ)^6231
        have hw : |(660276487/1250000000 : ℝ)|=(660276487/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1999064767/10000000000 : ℝ)|^8279 ≤ (2944172267387/25000000000000 : ℝ)^6231
        have hw : |(-1999064767/10000000000 : ℝ)|=(1999064767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(220764369/400000000 : ℝ)|^8279 ≤ (567461905083/1250000000000 : ℝ)^6231
        have hw : |(220764369/400000000 : ℝ)|=(220764369/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s2_6 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (52822121/100000000 : ℝ)*x 0 + (344944321/625000000 : ℝ)*x 1 + (-1999064609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52822121/100000000 : ℝ)^8279 ≤ (1070659017787/2500000000000 : ℝ)^6231 := by
    have hnat : (52822121 : ℕ)^8279*2500000000000^6231 ≤ 1070659017787^6231*100000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52822121 100000000 1070659017787 2500000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (344944321/625000000 : ℝ)^8279 ≤ (11349237858491/25000000000000 : ℝ)^6231 := by
    have hnat : (344944321 : ℕ)^8279*25000000000000^6231 ≤ 11349237858491^6231*625000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344944321 625000000 11349237858491 25000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1999064609/10000000000 : ℝ)^8279 ≤ (5888343916411/50000000000000 : ℝ)^6231 := by
    have hnat : (1999064609 : ℕ)^8279*50000000000000^6231 ≤ 5888343916411^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1999064609 10000000000 5888343916411 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52822121/100000000 : ℝ), (344944321/625000000 : ℝ), (-1999064609/10000000000 : ℝ)] ![(1070659017787/2500000000000 : ℝ), (11349237858491/25000000000000 : ℝ), (5888343916411/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52822121/100000000 : ℝ)|^8279 ≤ (1070659017787/2500000000000 : ℝ)^6231
        have hw : |(52822121/100000000 : ℝ)|=(52822121/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(344944321/625000000 : ℝ)|^8279 ≤ (11349237858491/25000000000000 : ℝ)^6231
        have hw : |(344944321/625000000 : ℝ)|=(344944321/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1999064609/10000000000 : ℝ)|^8279 ≤ (5888343916411/50000000000000 : ℝ)^6231
        have hw : |(-1999064609/10000000000 : ℝ)|=(1999064609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s2_7 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (436084853/1000000000 : ℝ)*x 0 + (148032993/312500000 : ℝ)*x 1 + (4015104677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436084853/1000000000 : ℝ)^8279 ≤ (33197508666383/100000000000000 : ℝ)^6231 := by
    have hnat : (436084853 : ℕ)^8279*100000000000000^6231 ≤ 33197508666383^6231*1000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436084853 1000000000 33197508666383 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (148032993/312500000 : ℝ)^8279 ≤ (18527844640867/50000000000000 : ℝ)^6231 := by
    have hnat : (148032993 : ℕ)^8279*50000000000000^6231 ≤ 18527844640867^6231*312500000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      148032993 312500000 18527844640867 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4015104677/10000000000 : ℝ)^8279 ≤ (5949360406661/20000000000000 : ℝ)^6231 := by
    have hnat : (4015104677 : ℕ)^8279*20000000000000^6231 ≤ 5949360406661^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4015104677 10000000000 5949360406661 20000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436084853/1000000000 : ℝ), (148032993/312500000 : ℝ), (4015104677/10000000000 : ℝ)] ![(33197508666383/100000000000000 : ℝ), (18527844640867/50000000000000 : ℝ), (5949360406661/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436084853/1000000000 : ℝ)|^8279 ≤ (33197508666383/100000000000000 : ℝ)^6231
        have hw : |(436084853/1000000000 : ℝ)|=(436084853/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(148032993/312500000 : ℝ)|^8279 ≤ (18527844640867/50000000000000 : ℝ)^6231
        have hw : |(148032993/312500000 : ℝ)|=(148032993/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4015104677/10000000000 : ℝ)|^8279 ≤ (5949360406661/20000000000000 : ℝ)^6231
        have hw : |(4015104677/10000000000 : ℝ)|=(4015104677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1086_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74191131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2587/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (533/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (8809/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4169/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2587/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (533/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2587/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (533/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2587/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (533/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2587/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (533/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2587/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (533/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2587/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (533/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (533/10000 : ℝ) ^ (4139/1024 : ℝ) ≤ (89197224181357/12500000000000000000 : ℝ) := by
    have hpowers : (533/10000 : ℝ)^4139 ≤ (89197224181357/12500000000000000000 : ℝ)^1024 := by
      have hnat : (533 : ℕ)^4139*12500000000000000000^1024 ≤ 89197224181357^1024*10000^4139 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        533 10000 89197224181357 12500000000000000000 4139 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (533/10000 : ℝ)) (X := (89197224181357/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2587/12500 : ℝ) ^ (4139/1024 : ℝ) ≤ (85859477505057521/50000000000000000000 : ℝ) := by
    have hpowers : (2587/12500 : ℝ)^4139 ≤ (85859477505057521/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2587 : ℕ)^4139*50000000000000000000^1024 ≤ 85859477505057521^1024*12500^4139 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2587 12500 85859477505057521 50000000000000000000 4139 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2587/12500 : ℝ)) (X := (85859477505057521/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250089197224181357/6250000000000000000 : ℝ) ≤ (2500008827008171/2500000000000000 : ℝ) ^ (4139/1024 : ℝ) := by
    have hpowers : (6250089197224181357/6250000000000000000 : ℝ)^1024 ≤ (2500008827008171/2500000000000000 : ℝ)^4139 := by
      have hnat : (6250089197224181357 : ℕ)^1024*2500000000000000^4139 ≤ 2500008827008171^4139*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250089197224181357 6250000000000000000 2500008827008171 2500000000000000 1024 4139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500008827008171/2500000000000000 : ℝ)) (X := (6250089197224181357/6250000000000000000 : ℝ)) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50086216266401782949/50000000000000000000 : ℝ) ≤ (10004263263079079/10000000000000000 : ℝ) ^ (4139/1024 : ℝ) := by
    have hpowers : (50086216266401782949/50000000000000000000 : ℝ)^1024 ≤ (10004263263079079/10000000000000000 : ℝ)^4139 := by
      have hnat : (50086216266401782949 : ℕ)^1024*10000000000000000^4139 ≤ 10004263263079079^4139*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50086216266401782949 50000000000000000000 10004263263079079 10000000000000000 1024 4139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004263263079079/10000000000000000 : ℝ)) (X := (50086216266401782949/50000000000000000000 : ℝ)) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25085859477505057521/25000000000000000000 : ℝ) ≤ (5004245609062737/5000000000000000 : ℝ) ^ (4139/1024 : ℝ) := by
    have hpowers : (25085859477505057521/25000000000000000000 : ℝ)^1024 ≤ (5004245609062737/5000000000000000 : ℝ)^4139 := by
      have hnat : (25085859477505057521 : ℕ)^1024*5000000000000000^4139 ≤ 5004245609062737^4139*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25085859477505057521 25000000000000000000 5004245609062737 5000000000000000 1024 4139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004245609062737/5000000000000000 : ℝ)) (X := (25085859477505057521/25000000000000000000 : ℝ)) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(89197224181357/12500000000000000000 : ℝ) ≤ ((2954143702739147147/2955000000000000000 : ℝ)+2*(845591009279/307320000000000 : ℝ)*(533/10000 : ℝ))^(4139/1024 : ℝ) := by
    rw [show (2954143702739147147/2955000000000000000 : ℝ)+2*(845591009279/307320000000000 : ℝ)*(533/10000 : ℝ)=(2500008827008171/2500000000000000 : ℝ) by norm_num, show 1+2*(89197224181357/12500000000000000000 : ℝ)=(6250089197224181357/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(85859477505057521/50000000000000000000 : ℝ)+(89197224181357/12500000000000000000 : ℝ) ≤ ((2954143702739147147/2955000000000000000 : ℝ)+(845591009279/307320000000000 : ℝ)*((2587/12500 : ℝ)+(533/10000 : ℝ)))^(4139/1024 : ℝ) := by
    rw [show (2954143702739147147/2955000000000000000 : ℝ)+(845591009279/307320000000000 : ℝ)*((2587/12500 : ℝ)+(533/10000 : ℝ))=(10004263263079079/10000000000000000 : ℝ) by norm_num, show 1+(85859477505057521/50000000000000000000 : ℝ)+(89197224181357/12500000000000000000 : ℝ)=(50086216266401782949/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(85859477505057521/50000000000000000000 : ℝ) ≤ ((2954143702739147147/2955000000000000000 : ℝ)+2*(845591009279/307320000000000 : ℝ)*(2587/12500 : ℝ))^(4139/1024 : ℝ) := by
    rw [show (2954143702739147147/2955000000000000000 : ℝ)+2*(845591009279/307320000000000 : ℝ)*(2587/12500 : ℝ)=(5004245609062737/5000000000000000 : ℝ) by norm_num, show 1+2*(85859477505057521/50000000000000000000 : ℝ)=(25085859477505057521/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2954143702739147147/2955000000000000000 : ℝ)*(X 1 0+X 2 0)+(845591009279/307320000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4139/1024 : ℝ)) (lo := (533/10000 : ℝ)) (hi := (2587/12500 : ℝ)) (c := (2954143702739147147/2955000000000000000 : ℝ)) (alpha := (845591009279/307320000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2954143702739147147/2955000000000000000 : ℝ)*(X 0 1+X 2 1)+(845591009279/307320000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4139/1024 : ℝ)) (lo := (533/10000 : ℝ)) (hi := (2587/12500 : ℝ)) (c := (2954143702739147147/2955000000000000000 : ℝ)) (alpha := (845591009279/307320000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2954143702739147147/2955000000000000000 : ℝ)*(X 0 2+X 1 2)+(845591009279/307320000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4139/1024 : ℝ)) (lo := (533/10000 : ℝ)) (hi := (2587/12500 : ℝ)) (c := (2954143702739147147/2955000000000000000 : ℝ)) (alpha := (845591009279/307320000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2174659833/10000000000 : ℝ)*X 0 0+(5521806939/10000000000 : ℝ)*X 0 1+(643691007/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1344077539/2500000000 : ℝ)*X 1 0+(-148040337/625000000 : ℝ)*X 1 1+(5149528617/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5376310291/10000000000 : ℝ)*X 2 0+(321845529/625000000 : ℝ)*X 2 1+(-2368645413/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4360613563/10000000000 : ℝ)*X 0 0+(4009797383/10000000000 : ℝ)*X 0 1+(237115447/500000000 : ℝ)*X 0 2+(4360613563/10000000000 : ℝ)*X 1 0+(4009797383/10000000000 : ℝ)*X 1 1+(237115447/500000000 : ℝ)*X 1 2+(4360613563/10000000000 : ℝ)*X 2 0+(4009797383/10000000000 : ℝ)*X 2 1+(237115447/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1087389571/5000000000 : ℝ)*X 0 0+(1288049537/2500000000 : ℝ)*X 0 1+(5519109133/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((660276487/1250000000 : ℝ)*X 1 0+(-1999064767/10000000000 : ℝ)*X 1 1+(220764369/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((52822121/100000000 : ℝ)*X 2 0+(344944321/625000000 : ℝ)*X 2 1+(-1999064609/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((436084853/1000000000 : ℝ)*X 0 0+(148032993/312500000 : ℝ)*X 0 1+(4015104677/10000000000 : ℝ)*X 0 2+(436084853/1000000000 : ℝ)*X 1 0+(148032993/312500000 : ℝ)*X 1 1+(4015104677/10000000000 : ℝ)*X 1 2+(436084853/1000000000 : ℝ)*X 2 0+(148032993/312500000 : ℝ)*X 2 1+(4015104677/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18107117508257189719677633/3201250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (949485269/100000000000000 : ℝ)*(base19) + (1008675551/100000000000000 : ℝ)*(base23) + (4440957/100000000000000 : ℝ)*(lower2) + (26147097/25000000000000 : ℝ)*(upper3) + (19966213/20000000000000 : ℝ)*(upper5) + (20256816039903/1000000000000 : ℝ)*(major0) + (20256816039903/1000000000000 : ℝ)*(major1) + (20256816039903/1000000000000 : ℝ)*(major2) + (2686171575305849/100000000000000 : ℝ)*(sp0) + (1343092167315873/50000000000000 : ℝ)*(sp1) + (335773034430183/12500000000000 : ℝ)*(sp2) + (1365171822590599/100000000000000 : ℝ)*(sp3) + (6854405583/50000000000000 : ℝ)*(sp4) + (739091353/12500000000000 : ℝ)*(sp7) + (1365177735321423/100000000000000 : ℝ)*(f.failure) + (537237056823403/20000000000000 : ℝ)*(f.sum) + (5336705674351/1280500000000000000000000000 : ℝ)*base65 + (68969140139095789/12805000000000000000000000000000 : ℝ)*base68 + (105026085431645789/12805000000000000000000000000000 : ℝ)*base70 + (62181807799060789/12805000000000000000000000000000 : ℝ)*base72 + (6626674395499/2561000000000000000000000000 : ℝ)*base74 + (42720754162945789/12805000000000000000000000000000 : ℝ)*base76 + (28330416038299211/12805000000000000000000000000000 : ℝ)*base77 + (20712531079280789/12805000000000000000000000000000 : ℝ)*base80 + (3179252030943/1280500000000000000000000000 : ℝ)*base82 + (20899413/5000000000000000000000 : ℝ)*base89 + (20899413/5000000000000000000000 : ℝ)*base91 + (20899413/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (388831325005693045398568013/49250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1560154331/100000000000000 : ℝ)*(base19) + (362535269/20000000000000 : ℝ)*(base23) + (107050629/50000000000000 : ℝ)*(upper3) + (49142251/100000000000000 : ℝ)*(lower4) + (157103123/100000000000000 : ℝ)*(upper5) + (2055295969987721/100000000000000 : ℝ)*(major0) + (2055295969987721/100000000000000 : ℝ)*(major1) + (2055295969987721/100000000000000 : ℝ)*(major2) + (13801077217/100000000000000 : ℝ)*(sp1) + (16845350551/100000000000000 : ℝ)*(sp2) + (681363945921359/25000000000000 : ℝ)*(sp4) + (21292503300421/781250000000 : ℝ)*(sp5) + (136271856282927/5000000000000 : ℝ)*(sp6) + (173141986640199/12500000000000 : ℝ)*(sp7) + (173141986640199/12500000000000 : ℝ)*(f.failure) + (681363945921359/25000000000000 : ℝ)*(f.sum) + (43706219745209/15366000000000000000000000000 : ℝ)*base66 + (3367336521681080277/1280500000000000000000000000000000 : ℝ)*base67 + (2923150468695080277/1280500000000000000000000000000000 : ℝ)*base69 + (3439723803188919723/1280500000000000000000000000000000 : ℝ)*base72 + (6921164076247/15366000000000000000000000000 : ℝ)*base73 + (12476386407064580277/1280500000000000000000000000000000 : ℝ)*base75 + (2837560146910580277/1280500000000000000000000000000000 : ℝ)*base77 + (2509175791886919723/1280500000000000000000000000000000 : ℝ)*base80 + (21435023815967/15366000000000000000000000000 : ℝ)*base82 + (2374931/625000000000000000000 : ℝ)*base90 + (2374931/625000000000000000000 : ℝ)*base92 + (2374931/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1086_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74191131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2587/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (533/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8809/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4169/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1086_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1086_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74191131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8809/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4169/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1086_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1086_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1086_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74191131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8809/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4169/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1086_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

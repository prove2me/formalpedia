-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1356_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:09:50.549884+00:00
-- url     : https://prove2.me/submissions/1be90d66-50aa-4147-b936-d340944412b5

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
theorem support_rectangle_w1356_s6_0 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-406386729/2000000000 : ℝ)*x 0 + (2705997329/5000000000 : ℝ)*x 1 + (524502101/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (406386729/2000000000 : ℝ)^1079 ≤ (3094353080989/25000000000000 : ℝ)^823 := by
    have hnat : (406386729 : ℕ)^1079*25000000000000^823 ≤ 3094353080989^823*2000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      406386729 2000000000 3094353080989 25000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705997329/5000000000 : ℝ)^1079 ≤ (44711194285441/100000000000000 : ℝ)^823 := by
    have hnat : (2705997329 : ℕ)^1079*100000000000000^823 ≤ 44711194285441^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705997329 5000000000 44711194285441 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524502101/1000000000 : ℝ)^1079 ≤ (42911393370543/100000000000000 : ℝ)^823 := by
    have hnat : (524502101 : ℕ)^1079*100000000000000^823 ≤ 42911393370543^823*1000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524502101 1000000000 42911393370543 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-406386729/2000000000 : ℝ), (2705997329/5000000000 : ℝ), (524502101/1000000000 : ℝ)] ![(3094353080989/25000000000000 : ℝ), (44711194285441/100000000000000 : ℝ), (42911393370543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-406386729/2000000000 : ℝ)|^1079 ≤ (3094353080989/25000000000000 : ℝ)^823
        have hw : |(-406386729/2000000000 : ℝ)|=(406386729/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705997329/5000000000 : ℝ)|^1079 ≤ (44711194285441/100000000000000 : ℝ)^823
        have hw : |(2705997329/5000000000 : ℝ)|=(2705997329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524502101/1000000000 : ℝ)|^1079 ≤ (42911393370543/100000000000000 : ℝ)^823
        have hw : |(524502101/1000000000 : ℝ)|=(524502101/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_s6_1 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (267437759/500000000 : ℝ)*x 0 + (-529249261/2500000000 : ℝ)*x 1 + (5245021017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267437759/500000000 : ℝ)^1079 ≤ (44027476814999/100000000000000 : ℝ)^823 := by
    have hnat : (267437759 : ℕ)^1079*100000000000000^823 ≤ 44027476814999^823*500000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267437759 500000000 44027476814999 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (529249261/2500000000 : ℝ)^1079 ≤ (816320607893/6250000000000 : ℝ)^823 := by
    have hnat : (529249261 : ℕ)^1079*6250000000000^823 ≤ 816320607893^823*2500000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529249261 2500000000 816320607893 6250000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245021017/10000000000 : ℝ)^1079 ≤ (42911393445627/100000000000000 : ℝ)^823 := by
    have hnat : (5245021017 : ℕ)^1079*100000000000000^823 ≤ 42911393445627^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245021017 10000000000 42911393445627 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267437759/500000000 : ℝ), (-529249261/2500000000 : ℝ), (5245021017/10000000000 : ℝ)] ![(44027476814999/100000000000000 : ℝ), (816320607893/6250000000000 : ℝ), (42911393445627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267437759/500000000 : ℝ)|^1079 ≤ (44027476814999/100000000000000 : ℝ)^823
        have hw : |(267437759/500000000 : ℝ)|=(267437759/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-529249261/2500000000 : ℝ)|^1079 ≤ (816320607893/6250000000000 : ℝ)^823
        have hw : |(-529249261/2500000000 : ℝ)|=(529249261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245021017/10000000000 : ℝ)|^1079 ≤ (42911393445627/100000000000000 : ℝ)^823
        have hw : |(5245021017/10000000000 : ℝ)|=(5245021017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_s6_2 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5348755187/10000000000 : ℝ)*x 0 + (5245021009/10000000000 : ℝ)*x 1 + (-423399409/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348755187/10000000000 : ℝ)^1079 ≤ (22013738445271/50000000000000 : ℝ)^823 := by
    have hnat : (5348755187 : ℕ)^1079*50000000000000^823 ≤ 22013738445271^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348755187 10000000000 22013738445271 50000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245021009/10000000000 : ℝ)^1079 ≤ (42911393359817/100000000000000 : ℝ)^823 := by
    have hnat : (5245021009 : ℕ)^1079*100000000000000^823 ≤ 42911393359817^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245021009 10000000000 42911393359817 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (423399409/2000000000 : ℝ)^1079 ≤ (13061129734377/100000000000000 : ℝ)^823 := by
    have hnat : (423399409 : ℕ)^1079*100000000000000^823 ≤ 13061129734377^823*2000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423399409 2000000000 13061129734377 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348755187/10000000000 : ℝ), (5245021009/10000000000 : ℝ), (-423399409/2000000000 : ℝ)] ![(22013738445271/50000000000000 : ℝ), (42911393359817/100000000000000 : ℝ), (13061129734377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348755187/10000000000 : ℝ)|^1079 ≤ (22013738445271/50000000000000 : ℝ)^823
        have hw : |(5348755187/10000000000 : ℝ)|=(5348755187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245021009/10000000000 : ℝ)|^1079 ≤ (42911393359817/100000000000000 : ℝ)^823
        have hw : |(5245021009/10000000000 : ℝ)|=(5245021009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-423399409/2000000000 : ℝ)|^1079 ≤ (13061129734377/100000000000000 : ℝ)^823
        have hw : |(-423399409/2000000000 : ℝ)|=(423399409/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_s6_3 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2161485433/5000000000 : ℝ)*x 0 + (4150499767/10000000000 : ℝ)*x 1 + (2251040633/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2161485433/5000000000 : ℝ)^1079 ≤ (1332139782869/4000000000000 : ℝ)^823 := by
    have hnat : (2161485433 : ℕ)^1079*4000000000000^823 ≤ 1332139782869^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161485433 5000000000 1332139782869 4000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4150499767/10000000000 : ℝ)^1079 ≤ (7893103822909/25000000000000 : ℝ)^823 := by
    have hnat : (4150499767 : ℕ)^1079*25000000000000^823 ≤ 7893103822909^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4150499767 10000000000 7893103822909 25000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2251040633/5000000000 : ℝ)^1079 ≤ (3512409012311/10000000000000 : ℝ)^823 := by
    have hnat : (2251040633 : ℕ)^1079*10000000000000^823 ≤ 3512409012311^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251040633 5000000000 3512409012311 10000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2161485433/5000000000 : ℝ), (4150499767/10000000000 : ℝ), (2251040633/5000000000 : ℝ)] ![(1332139782869/4000000000000 : ℝ), (7893103822909/25000000000000 : ℝ), (3512409012311/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2161485433/5000000000 : ℝ)|^1079 ≤ (1332139782869/4000000000000 : ℝ)^823
        have hw : |(2161485433/5000000000 : ℝ)|=(2161485433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4150499767/10000000000 : ℝ)|^1079 ≤ (7893103822909/25000000000000 : ℝ)^823
        have hw : |(4150499767/10000000000 : ℝ)|=(4150499767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2251040633/5000000000 : ℝ)|^1079 ≤ (3512409012311/10000000000000 : ℝ)^823
        have hw : |(2251040633/5000000000 : ℝ)|=(2251040633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_s6_4 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2031945683/10000000000 : ℝ)*x 0 + (327851221/625000000 : ℝ)*x 1 + (2705696521/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2031945683/10000000000 : ℝ)^1079 ≤ (12377508462311/100000000000000 : ℝ)^823 := by
    have hnat : (2031945683 : ℕ)^1079*100000000000000^823 ≤ 12377508462311^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2031945683 10000000000 12377508462311 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327851221/625000000 : ℝ)^1079 ≤ (42917813410373/100000000000000 : ℝ)^823 := by
    have hnat : (327851221 : ℕ)^1079*100000000000000^823 ≤ 42917813410373^823*625000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327851221 625000000 42917813410373 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705696521/5000000000 : ℝ)^1079 ≤ (22352339057843/50000000000000 : ℝ)^823 := by
    have hnat : (2705696521 : ℕ)^1079*50000000000000^823 ≤ 22352339057843^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705696521 5000000000 22352339057843 50000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2031945683/10000000000 : ℝ), (327851221/625000000 : ℝ), (2705696521/5000000000 : ℝ)] ![(12377508462311/100000000000000 : ℝ), (42917813410373/100000000000000 : ℝ), (22352339057843/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2031945683/10000000000 : ℝ)|^1079 ≤ (12377508462311/100000000000000 : ℝ)^823
        have hw : |(-2031945683/10000000000 : ℝ)|=(2031945683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327851221/625000000 : ℝ)|^1079 ≤ (42917813410373/100000000000000 : ℝ)^823
        have hw : |(327851221/625000000 : ℝ)|=(327851221/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705696521/5000000000 : ℝ)|^1079 ≤ (22352339057843/50000000000000 : ℝ)^823
        have hw : |(2705696521/5000000000 : ℝ)|=(2705696521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_s6_5 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (53056779/100000000 : ℝ)*x 0 + (-1950625017/10000000000 : ℝ)*x 1 + (1082278609/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53056779/100000000 : ℝ)^1079 ≤ (1361349377859/3125000000000 : ℝ)^823 := by
    have hnat : (53056779 : ℕ)^1079*3125000000000^823 ≤ 1361349377859^823*100000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53056779 100000000 1361349377859 3125000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1950625017/10000000000 : ℝ)^1079 ≤ (11732141749871/100000000000000 : ℝ)^823 := by
    have hnat : (1950625017 : ℕ)^1079*100000000000000^823 ≤ 11732141749871^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1950625017 10000000000 11732141749871 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082278609/2000000000 : ℝ)^1079 ≤ (44704678148179/100000000000000 : ℝ)^823 := by
    have hnat : (1082278609 : ℕ)^1079*100000000000000^823 ≤ 44704678148179^823*2000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082278609 2000000000 44704678148179 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53056779/100000000 : ℝ), (-1950625017/10000000000 : ℝ), (1082278609/2000000000 : ℝ)] ![(1361349377859/3125000000000 : ℝ), (11732141749871/100000000000000 : ℝ), (44704678148179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53056779/100000000 : ℝ)|^1079 ≤ (1361349377859/3125000000000 : ℝ)^823
        have hw : |(53056779/100000000 : ℝ)|=(53056779/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1950625017/10000000000 : ℝ)|^1079 ≤ (11732141749871/100000000000000 : ℝ)^823
        have hw : |(-1950625017/10000000000 : ℝ)|=(1950625017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082278609/2000000000 : ℝ)|^1079 ≤ (44704678148179/100000000000000 : ℝ)^823
        have hw : |(1082278609/2000000000 : ℝ)|=(1082278609/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_s6_6 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1326419477/2500000000 : ℝ)*x 0 + (1082278607/2000000000 : ℝ)*x 1 + (-1950625019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326419477/2500000000 : ℝ)^1079 ≤ (8712636035521/20000000000000 : ℝ)^823 := by
    have hnat : (1326419477 : ℕ)^1079*20000000000000^823 ≤ 8712636035521^823*2500000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326419477 2500000000 8712636035521 20000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082278607/2000000000 : ℝ)^1079 ≤ (4470467803987/10000000000000 : ℝ)^823 := by
    have hnat : (1082278607 : ℕ)^1079*10000000000000^823 ≤ 4470467803987^823*2000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082278607 2000000000 4470467803987 10000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1950625019/10000000000 : ℝ)^1079 ≤ (5866070882821/50000000000000 : ℝ)^823 := by
    have hnat : (1950625019 : ℕ)^1079*50000000000000^823 ≤ 5866070882821^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1950625019 10000000000 5866070882821 50000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326419477/2500000000 : ℝ), (1082278607/2000000000 : ℝ), (-1950625019/10000000000 : ℝ)] ![(8712636035521/20000000000000 : ℝ), (4470467803987/10000000000000 : ℝ), (5866070882821/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326419477/2500000000 : ℝ)|^1079 ≤ (8712636035521/20000000000000 : ℝ)^823
        have hw : |(1326419477/2500000000 : ℝ)|=(1326419477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082278607/2000000000 : ℝ)|^1079 ≤ (4470467803987/10000000000000 : ℝ)^823
        have hw : |(1082278607/2000000000 : ℝ)|=(1082278607/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1950625019/10000000000 : ℝ)|^1079 ≤ (5866070882821/50000000000000 : ℝ)^823
        have hw : |(-1950625019/10000000000 : ℝ)|=(1950625019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_s6_7 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2161498099/5000000000 : ℝ)*x 0 + (4500820993/10000000000 : ℝ)*x 1 + (83035331/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2161498099/5000000000 : ℝ)^1079 ≤ (16651875214857/50000000000000 : ℝ)^823 := by
    have hnat : (2161498099 : ℕ)^1079*50000000000000^823 ≤ 16651875214857^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161498099 5000000000 16651875214857 50000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4500820993/10000000000 : ℝ)^1079 ≤ (17555599970031/50000000000000 : ℝ)^823 := by
    have hnat : (4500820993 : ℕ)^1079*50000000000000^823 ≤ 17555599970031^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500820993 10000000000 17555599970031 50000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (83035331/200000000 : ℝ)^1079 ≤ (31585049611351/100000000000000 : ℝ)^823 := by
    have hnat : (83035331 : ℕ)^1079*100000000000000^823 ≤ 31585049611351^823*200000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83035331 200000000 31585049611351 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2161498099/5000000000 : ℝ), (4500820993/10000000000 : ℝ), (83035331/200000000 : ℝ)] ![(16651875214857/50000000000000 : ℝ), (17555599970031/50000000000000 : ℝ), (31585049611351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2161498099/5000000000 : ℝ)|^1079 ≤ (16651875214857/50000000000000 : ℝ)^823
        have hw : |(2161498099/5000000000 : ℝ)|=(2161498099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4500820993/10000000000 : ℝ)|^1079 ≤ (17555599970031/50000000000000 : ℝ)^823
        have hw : |(4500820993/10000000000 : ℝ)|=(4500820993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(83035331/200000000 : ℝ)|^1079 ≤ (31585049611351/100000000000000 : ℝ)^823
        have hw : |(83035331/200000000 : ℝ)|=(83035331/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1356_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77640267/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14723/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (447/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (11181/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3679/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14723/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (447/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14723/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (447/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14723/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (447/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14723/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (447/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14723/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (447/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14723/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (447/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (447/4000 : ℝ) ^ (4315/1024 : ℝ) ≤ (975981315889911/10000000000000000000 : ℝ) := by
    have hpowers : (447/4000 : ℝ)^4315 ≤ (975981315889911/10000000000000000000 : ℝ)^1024 := by
      have hnat : (447 : ℕ)^4315*10000000000000000000^1024 ≤ 975981315889911^1024*4000^4315 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        447 4000 975981315889911 10000000000000000000 4315 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (447/4000 : ℝ)) (X := (975981315889911/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4315 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14723/100000 : ℝ) ^ (4315/1024 : ℝ) ≤ (6238453686546461/20000000000000000000 : ℝ) := by
    have hpowers : (14723/100000 : ℝ)^4315 ≤ (6238453686546461/20000000000000000000 : ℝ)^1024 := by
      have hnat : (14723 : ℕ)^4315*20000000000000000000^1024 ≤ 6238453686546461^1024*100000^4315 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14723 100000 6238453686546461 20000000000000000000 4315 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14723/100000 : ℝ)) (X := (6238453686546461/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4315 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000975981315889911/5000000000000000000 : ℝ) ≤ (10000463189100047/10000000000000000 : ℝ) ^ (4315/1024 : ℝ) := by
    have hpowers : (5000975981315889911/5000000000000000000 : ℝ)^1024 ≤ (10000463189100047/10000000000000000 : ℝ)^4315 := by
      have hnat : (5000975981315889911 : ℕ)^1024*10000000000000000^4315 ≤ 10000463189100047^4315*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000975981315889911 5000000000000000000 10000463189100047 10000000000000000 1024 4315 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000463189100047/10000000000000000 : ℝ)) (X := (5000975981315889911/5000000000000000000 : ℝ)) (by norm_num) 4315 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008190416318326283/20000000000000000000 : ℝ) ≤ (10000971689089581/10000000000000000 : ℝ) ^ (4315/1024 : ℝ) := by
    have hpowers : (20008190416318326283/20000000000000000000 : ℝ)^1024 ≤ (10000971689089581/10000000000000000 : ℝ)^4315 := by
      have hnat : (20008190416318326283 : ℕ)^1024*10000000000000000^4315 ≤ 10000971689089581^4315*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008190416318326283 20000000000000000000 10000971689089581 10000000000000000 1024 4315 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000971689089581/10000000000000000 : ℝ)) (X := (20008190416318326283/20000000000000000000 : ℝ)) (by norm_num) 4315 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006238453686546461/10000000000000000000 : ℝ) ≤ (2000296037815823/2000000000000000 : ℝ) ^ (4315/1024 : ℝ) := by
    have hpowers : (10006238453686546461/10000000000000000000 : ℝ)^1024 ≤ (2000296037815823/2000000000000000 : ℝ)^4315 := by
      have hnat : (10006238453686546461 : ℕ)^1024*2000000000000000^4315 ≤ 2000296037815823^4315*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006238453686546461 10000000000000000000 2000296037815823 2000000000000000 1024 4315 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000296037815823/2000000000000000 : ℝ)) (X := (10006238453686546461/10000000000000000000 : ℝ)) (by norm_num) 4315 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(975981315889911/10000000000000000000 : ℝ) ≤ ((554223100315013779/554375000000000000 : ℝ)+2*(254249994767/177400000000000 : ℝ)*(447/4000 : ℝ))^(4315/1024 : ℝ) := by
    rw [show (554223100315013779/554375000000000000 : ℝ)+2*(254249994767/177400000000000 : ℝ)*(447/4000 : ℝ)=(10000463189100047/10000000000000000 : ℝ) by norm_num, show 1+2*(975981315889911/10000000000000000000 : ℝ)=(5000975981315889911/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6238453686546461/20000000000000000000 : ℝ)+(975981315889911/10000000000000000000 : ℝ) ≤ ((554223100315013779/554375000000000000 : ℝ)+(254249994767/177400000000000 : ℝ)*((14723/100000 : ℝ)+(447/4000 : ℝ)))^(4315/1024 : ℝ) := by
    rw [show (554223100315013779/554375000000000000 : ℝ)+(254249994767/177400000000000 : ℝ)*((14723/100000 : ℝ)+(447/4000 : ℝ))=(10000971689089581/10000000000000000 : ℝ) by norm_num, show 1+(6238453686546461/20000000000000000000 : ℝ)+(975981315889911/10000000000000000000 : ℝ)=(20008190416318326283/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6238453686546461/20000000000000000000 : ℝ) ≤ ((554223100315013779/554375000000000000 : ℝ)+2*(254249994767/177400000000000 : ℝ)*(14723/100000 : ℝ))^(4315/1024 : ℝ) := by
    rw [show (554223100315013779/554375000000000000 : ℝ)+2*(254249994767/177400000000000 : ℝ)*(14723/100000 : ℝ)=(2000296037815823/2000000000000000 : ℝ) by norm_num, show 1+2*(6238453686546461/20000000000000000000 : ℝ)=(10006238453686546461/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (554223100315013779/554375000000000000 : ℝ)*(X 1 0+X 2 0)+(254249994767/177400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4315/1024 : ℝ)) (lo := (447/4000 : ℝ)) (hi := (14723/100000 : ℝ)) (c := (554223100315013779/554375000000000000 : ℝ)) (alpha := (254249994767/177400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (554223100315013779/554375000000000000 : ℝ)*(X 0 1+X 2 1)+(254249994767/177400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4315/1024 : ℝ)) (lo := (447/4000 : ℝ)) (hi := (14723/100000 : ℝ)) (c := (554223100315013779/554375000000000000 : ℝ)) (alpha := (254249994767/177400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (554223100315013779/554375000000000000 : ℝ)*(X 0 2+X 1 2)+(254249994767/177400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4315/1024 : ℝ)) (lo := (447/4000 : ℝ)) (hi := (14723/100000 : ℝ)) (c := (554223100315013779/554375000000000000 : ℝ)) (alpha := (254249994767/177400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-406386729/2000000000 : ℝ)*X 0 0+(2705997329/5000000000 : ℝ)*X 0 1+(524502101/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267437759/500000000 : ℝ)*X 1 0+(-529249261/2500000000 : ℝ)*X 1 1+(5245021017/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348755187/10000000000 : ℝ)*X 2 0+(5245021009/10000000000 : ℝ)*X 2 1+(-423399409/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2161485433/5000000000 : ℝ)*X 0 0+(4150499767/10000000000 : ℝ)*X 0 1+(2251040633/5000000000 : ℝ)*X 0 2+(2161485433/5000000000 : ℝ)*X 1 0+(4150499767/10000000000 : ℝ)*X 1 1+(2251040633/5000000000 : ℝ)*X 1 2+(2161485433/5000000000 : ℝ)*X 2 0+(4150499767/10000000000 : ℝ)*X 2 1+(2251040633/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2031945683/10000000000 : ℝ)*X 0 0+(327851221/625000000 : ℝ)*X 0 1+(2705696521/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((53056779/100000000 : ℝ)*X 1 0+(-1950625017/10000000000 : ℝ)*X 1 1+(1082278609/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326419477/2500000000 : ℝ)*X 2 0+(1082278607/2000000000 : ℝ)*X 2 1+(-1950625019/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2161498099/5000000000 : ℝ)*X 0 0+(4500820993/10000000000 : ℝ)*X 0 1+(83035331/200000000 : ℝ)*X 0 2+(2161498099/5000000000 : ℝ)*X 1 0+(4500820993/10000000000 : ℝ)*X 1 1+(83035331/200000000 : ℝ)*X 1 2+(2161498099/5000000000 : ℝ)*X 2 0+(4500820993/10000000000 : ℝ)*X 2 1+(83035331/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (58287735451138050929581689/6929687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (314764547/20000000000000 : ℝ)*(base19) + (1467342663/100000000000000 : ℝ)*(base23) + (61145909/100000000000000 : ℝ)*(lower2) + (213452997/100000000000000 : ℝ)*(upper3) + (64669481/50000000000000 : ℝ)*(upper5) + (2208339482881097/50000000000000 : ℝ)*(major0) + (2208339482881097/50000000000000 : ℝ)*(major1) + (2208339482881097/50000000000000 : ℝ)*(major2) + (1497250719483407/25000000000000 : ℝ)*(sp0) + (2994516853358153/50000000000000 : ℝ)*(sp1) + (2994516906598189/50000000000000 : ℝ)*(sp2) + (284430562520563/10000000000000 : ℝ)*(sp3) + (32402605413/100000000000000 : ℝ)*(sp4) + (8372701389/50000000000000 : ℝ)*(sp7) + (355540296326051/12500000000000 : ℝ)*(f.failure) + (5989035280539041/100000000000000 : ℝ)*(f.sum) + (340694323339/277187500000000000000000000 : ℝ)*base65 + (113916011660558781/13859375000000000000000000000000 : ℝ)*base68 + (180368246476965031/13859375000000000000000000000000 : ℝ)*base70 + (183956640983621281/13859375000000000000000000000000 : ℝ)*base72 + (5262666843899/4435000000000000000000000000 : ℝ)*base73 + (183158728741215031/13859375000000000000000000000000 : ℝ)*base76 + (46536578914472469/13859375000000000000000000000000 : ℝ)*base77 + (134788200058527531/13859375000000000000000000000000 : ℝ)*base80 + (24057531365051/4435000000000000000000000000 : ℝ)*base82 + (6195617/625000000000000000000 : ℝ)*base89 + (6195617/625000000000000000000 : ℝ)*base91 + (6195617/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (62615519828435459243555529/13859375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24376237/3125000000000 : ℝ)*(base19) + (106803703/12500000000000 : ℝ)*(base23) + (88602589/100000000000000 : ℝ)*(upper3) + (6081469/20000000000000 : ℝ)*(lower4) + (47403017/50000000000000 : ℝ)*(upper5) + (556075573372177/12500000000000 : ℝ)*(major0) + (556075573372177/12500000000000 : ℝ)*(major1) + (556075573372177/12500000000000 : ℝ)*(major2) + (1629700727/10000000000000 : ℝ)*(sp1) + (1080018699/6250000000000 : ℝ)*(sp2) + (6032326689183319/100000000000000 : ℝ)*(sp4) + (377019350758529/6250000000000 : ℝ)*(sp5) + (377019284653407/6250000000000 : ℝ)*(sp6) + (1432441167087117/50000000000000 : ℝ)*(sp7) + (1432441167087117/50000000000000 : ℝ)*(f.failure) + (6032326689183319/100000000000000 : ℝ)*(f.sum) + (5723525073111/4435000000000000000000000000 : ℝ)*base65 + (27068150201323117/6929687500000000000000000000000 : ℝ)*base68 + (42800252493801883/6929687500000000000000000000000 : ℝ)*base69 + (460946970855547/108276367187500000000000000000 : ℝ)*base71 + (2371901441677/2217500000000000000000000000 : ℝ)*base74 + (76525516526114383/6929687500000000000000000000000 : ℝ)*base75 + (7544783173829377/1732421875000000000000000000000 : ℝ)*base77 + (84688228678698117/6929687500000000000000000000000 : ℝ)*base80 + (5632400268377/554375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (23859761/2500000000000000000000 : ℝ)*base90 + (23859761/2500000000000000000000 : ℝ)*base92 + (23859761/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1356_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77640267/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14723/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (447/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11181/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3679/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1356_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1356_s7_0 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2031941329/10000000000 : ℝ)*x 0 + (5411940797/10000000000 : ℝ)*x 1 + (2622534839/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2031941329/10000000000 : ℝ)^1079 ≤ (6188736845101/50000000000000 : ℝ)^823 := by
    have hnat : (2031941329 : ℕ)^1079*50000000000000^823 ≤ 6188736845101^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2031941329 10000000000 6188736845101 50000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411940797/10000000000 : ℝ)^1079 ≤ (44710610901781/100000000000000 : ℝ)^823 := by
    have hnat : (5411940797 : ℕ)^1079*100000000000000^823 ≤ 44710610901781^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411940797 10000000000 44710610901781 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622534839/5000000000 : ℝ)^1079 ≤ (10727978848831/25000000000000 : ℝ)^823 := by
    have hnat : (2622534839 : ℕ)^1079*25000000000000^823 ≤ 10727978848831^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622534839 5000000000 10727978848831 25000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2031941329/10000000000 : ℝ), (5411940797/10000000000 : ℝ), (2622534839/5000000000 : ℝ)] ![(6188736845101/50000000000000 : ℝ), (44710610901781/100000000000000 : ℝ), (10727978848831/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2031941329/10000000000 : ℝ)|^1079 ≤ (6188736845101/50000000000000 : ℝ)^823
        have hw : |(-2031941329/10000000000 : ℝ)|=(2031941329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411940797/10000000000 : ℝ)|^1079 ≤ (44710610901781/100000000000000 : ℝ)^823
        have hw : |(5411940797/10000000000 : ℝ)|=(5411940797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622534839/5000000000 : ℝ)|^1079 ≤ (10727978848831/25000000000000 : ℝ)^823
        have hw : |(2622534839/5000000000 : ℝ)|=(2622534839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_s7_1 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1069748183/2000000000 : ℝ)*x 0 + (-4134671/19531250 : ℝ)*x 1 + (2622534837/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069748183/2000000000 : ℝ)^1079 ≤ (22013661435231/50000000000000 : ℝ)^823 := by
    have hnat : (1069748183 : ℕ)^1079*50000000000000^823 ≤ 22013661435231^823*2000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069748183 2000000000 22013661435231 50000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4134671/19531250 : ℝ)^1079 ≤ (163259521919/1250000000000 : ℝ)^823 := by
    have hnat : (4134671 : ℕ)^1079*1250000000000^823 ≤ 163259521919^823*19531250^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4134671 19531250 163259521919 1250000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622534837/5000000000 : ℝ)^1079 ≤ (42911915352419/100000000000000 : ℝ)^823 := by
    have hnat : (2622534837 : ℕ)^1079*100000000000000^823 ≤ 42911915352419^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622534837 5000000000 42911915352419 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069748183/2000000000 : ℝ), (-4134671/19531250 : ℝ), (2622534837/5000000000 : ℝ)] ![(22013661435231/50000000000000 : ℝ), (163259521919/1250000000000 : ℝ), (42911915352419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069748183/2000000000 : ℝ)|^1079 ≤ (22013661435231/50000000000000 : ℝ)^823
        have hw : |(1069748183/2000000000 : ℝ)|=(1069748183/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4134671/19531250 : ℝ)|^1079 ≤ (163259521919/1250000000000 : ℝ)^823
        have hw : |(-4134671/19531250 : ℝ)|=(4134671/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622534837/5000000000 : ℝ)|^1079 ≤ (42911915352419/100000000000000 : ℝ)^823
        have hw : |(2622534837/5000000000 : ℝ)|=(2622534837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_s7_2 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (668592617/1250000000 : ℝ)*x 0 + (1049013933/2000000000 : ℝ)*x 1 + (-2116951537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668592617/1250000000 : ℝ)^1079 ≤ (44027323097089/100000000000000 : ℝ)^823 := by
    have hnat : (668592617 : ℕ)^1079*100000000000000^823 ≤ 44027323097089^823*1250000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668592617 1250000000 44027323097089 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049013933/2000000000 : ℝ)^1079 ≤ (42911915255883/100000000000000 : ℝ)^823 := by
    have hnat : (1049013933 : ℕ)^1079*100000000000000^823 ≤ 42911915255883^823*2000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049013933 2000000000 42911915255883 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2116951537/10000000000 : ℝ)^1079 ≤ (13060761632189/100000000000000 : ℝ)^823 := by
    have hnat : (2116951537 : ℕ)^1079*100000000000000^823 ≤ 13060761632189^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116951537 10000000000 13060761632189 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668592617/1250000000 : ℝ), (1049013933/2000000000 : ℝ), (-2116951537/10000000000 : ℝ)] ![(44027323097089/100000000000000 : ℝ), (42911915255883/100000000000000 : ℝ), (13060761632189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668592617/1250000000 : ℝ)|^1079 ≤ (44027323097089/100000000000000 : ℝ)^823
        have hw : |(668592617/1250000000 : ℝ)|=(668592617/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049013933/2000000000 : ℝ)|^1079 ≤ (42911915255883/100000000000000 : ℝ)^823
        have hw : |(1049013933/2000000000 : ℝ)|=(1049013933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2116951537/10000000000 : ℝ)|^1079 ≤ (13060761632189/100000000000000 : ℝ)^823
        have hw : |(-2116951537/10000000000 : ℝ)|=(2116951537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_s7_3 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4322974489/10000000000 : ℝ)*x 0 + (4150607263/10000000000 : ℝ)*x 1 + (1125493219/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4322974489/10000000000 : ℝ)^1079 ≤ (33303531164681/100000000000000 : ℝ)^823 := by
    have hnat : (4322974489 : ℕ)^1079*100000000000000^823 ≤ 33303531164681^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4322974489 10000000000 33303531164681 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4150607263/10000000000 : ℝ)^1079 ≤ (3157348736147/10000000000000 : ℝ)^823 := by
    have hnat : (4150607263 : ℕ)^1079*10000000000000^823 ≤ 3157348736147^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4150607263 10000000000 3157348736147 10000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1125493219/2500000000 : ℝ)^1079 ≤ (1756149072827/5000000000000 : ℝ)^823 := by
    have hnat : (1125493219 : ℕ)^1079*5000000000000^823 ≤ 1756149072827^823*2500000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125493219 2500000000 1756149072827 5000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4322974489/10000000000 : ℝ), (4150607263/10000000000 : ℝ), (1125493219/2500000000 : ℝ)] ![(33303531164681/100000000000000 : ℝ), (3157348736147/10000000000000 : ℝ), (1756149072827/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4322974489/10000000000 : ℝ)|^1079 ≤ (33303531164681/100000000000000 : ℝ)^823
        have hw : |(4322974489/10000000000 : ℝ)|=(4322974489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4150607263/10000000000 : ℝ)|^1079 ≤ (3157348736147/10000000000000 : ℝ)^823
        have hw : |(4150607263/10000000000 : ℝ)|=(4150607263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1125493219/2500000000 : ℝ)|^1079 ≤ (1756149072827/5000000000000 : ℝ)^823
        have hw : |(1125493219/2500000000 : ℝ)|=(1125493219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_s7_4 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2031953489/10000000000 : ℝ)*x 0 + (5245667371/10000000000 : ℝ)*x 1 + (676417489/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2031953489/10000000000 : ℝ)^1079 ≤ (12377570802993/100000000000000 : ℝ)^823 := by
    have hnat : (2031953489 : ℕ)^1079*100000000000000^823 ≤ 12377570802993^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2031953489 10000000000 12377570802993 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245667371/10000000000 : ℝ)^1079 ≤ (42918326518393/100000000000000 : ℝ)^823 := by
    have hnat : (5245667371 : ℕ)^1079*100000000000000^823 ≤ 42918326518393^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245667371 10000000000 42918326518393 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676417489/1250000000 : ℝ)^1079 ≤ (2235205133479/5000000000000 : ℝ)^823 := by
    have hnat : (676417489 : ℕ)^1079*5000000000000^823 ≤ 2235205133479^823*1250000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676417489 1250000000 2235205133479 5000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2031953489/10000000000 : ℝ), (5245667371/10000000000 : ℝ), (676417489/1250000000 : ℝ)] ![(12377570802993/100000000000000 : ℝ), (42918326518393/100000000000000 : ℝ), (2235205133479/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2031953489/10000000000 : ℝ)|^1079 ≤ (12377570802993/100000000000000 : ℝ)^823
        have hw : |(-2031953489/10000000000 : ℝ)|=(2031953489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245667371/10000000000 : ℝ)|^1079 ≤ (42918326518393/100000000000000 : ℝ)^823
        have hw : |(5245667371/10000000000 : ℝ)|=(5245667371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676417489/1250000000 : ℝ)|^1079 ≤ (2235205133479/5000000000000 : ℝ)^823
        have hw : |(676417489/1250000000 : ℝ)|=(676417489/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_s7_5 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2652845141/5000000000 : ℝ)*x 0 + (-1950681207/10000000000 : ℝ)*x 1 + (5411339829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652845141/5000000000 : ℝ)^1079 ≤ (43563313379553/100000000000000 : ℝ)^823 := by
    have hnat : (2652845141 : ℕ)^1079*100000000000000^823 ≤ 43563313379553^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652845141 5000000000 43563313379553 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1950681207/10000000000 : ℝ)^1079 ≤ (11732584833903/100000000000000 : ℝ)^823 := by
    have hnat : (1950681207 : ℕ)^1079*100000000000000^823 ≤ 11732584833903^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1950681207 10000000000 11732584833903 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411339829/10000000000 : ℝ)^1079 ≤ (5588012721327/12500000000000 : ℝ)^823 := by
    have hnat : (5411339829 : ℕ)^1079*12500000000000^823 ≤ 5588012721327^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411339829 10000000000 5588012721327 12500000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652845141/5000000000 : ℝ), (-1950681207/10000000000 : ℝ), (5411339829/10000000000 : ℝ)] ![(43563313379553/100000000000000 : ℝ), (11732584833903/100000000000000 : ℝ), (5588012721327/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652845141/5000000000 : ℝ)|^1079 ≤ (43563313379553/100000000000000 : ℝ)^823
        have hw : |(2652845141/5000000000 : ℝ)|=(2652845141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1950681207/10000000000 : ℝ)|^1079 ≤ (11732584833903/100000000000000 : ℝ)^823
        have hw : |(-1950681207/10000000000 : ℝ)|=(1950681207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411339829/10000000000 : ℝ)|^1079 ≤ (5588012721327/12500000000000 : ℝ)^823
        have hw : |(5411339829/10000000000 : ℝ)|=(5411339829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_s7_6 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2652845139/5000000000 : ℝ)*x 0 + (338208737/625000000 : ℝ)*x 1 + (-121917579/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652845139/5000000000 : ℝ)^1079 ≤ (21781656668247/50000000000000 : ℝ)^823 := by
    have hnat : (2652845139 : ℕ)^1079*50000000000000^823 ≤ 21781656668247^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652845139 5000000000 21781656668247 50000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338208737/625000000 : ℝ)^1079 ≤ (44704101369873/100000000000000 : ℝ)^823 := by
    have hnat : (338208737 : ℕ)^1079*100000000000000^823 ≤ 44704101369873^823*625000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338208737 625000000 44704101369873 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (121917579/625000000 : ℝ)^1079 ≤ (733286580211/6250000000000 : ℝ)^823 := by
    have hnat : (121917579 : ℕ)^1079*6250000000000^823 ≤ 733286580211^823*625000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121917579 625000000 733286580211 6250000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652845139/5000000000 : ℝ), (338208737/625000000 : ℝ), (-121917579/625000000 : ℝ)] ![(21781656668247/50000000000000 : ℝ), (44704101369873/100000000000000 : ℝ), (733286580211/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652845139/5000000000 : ℝ)|^1079 ≤ (21781656668247/50000000000000 : ℝ)^823
        have hw : |(2652845139/5000000000 : ℝ)|=(2652845139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338208737/625000000 : ℝ)|^1079 ≤ (44704101369873/100000000000000 : ℝ)^823
        have hw : |(338208737/625000000 : ℝ)|=(338208737/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-121917579/625000000 : ℝ)|^1079 ≤ (733286580211/6250000000000 : ℝ)^823
        have hw : |(-121917579/625000000 : ℝ)|=(121917579/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_s7_7 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (172919991/400000000 : ℝ)*x 0 + (4500714193/10000000000 : ℝ)*x 1 + (1037968111/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172919991/400000000 : ℝ)^1079 ≤ (2081486659883/6250000000000 : ℝ)^823 := by
    have hnat : (172919991 : ℕ)^1079*6250000000000^823 ≤ 2081486659883^823*400000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172919991 400000000 2081486659883 6250000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4500714193/10000000000 : ℝ)^1079 ≤ (3511010763187/10000000000000 : ℝ)^823 := by
    have hnat : (4500714193 : ℕ)^1079*10000000000000^823 ≤ 3511010763187^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500714193 10000000000 3511010763187 10000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1037968111/2500000000 : ℝ)^1079 ≤ (6317221160889/20000000000000 : ℝ)^823 := by
    have hnat : (1037968111 : ℕ)^1079*20000000000000^823 ≤ 6317221160889^823*2500000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037968111 2500000000 6317221160889 20000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(172919991/400000000 : ℝ), (4500714193/10000000000 : ℝ), (1037968111/2500000000 : ℝ)] ![(2081486659883/6250000000000 : ℝ), (3511010763187/10000000000000 : ℝ), (6317221160889/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(172919991/400000000 : ℝ)|^1079 ≤ (2081486659883/6250000000000 : ℝ)^823
        have hw : |(172919991/400000000 : ℝ)|=(172919991/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4500714193/10000000000 : ℝ)|^1079 ≤ (3511010763187/10000000000000 : ℝ)^823
        have hw : |(4500714193/10000000000 : ℝ)|=(4500714193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1037968111/2500000000 : ℝ)|^1079 ≤ (6317221160889/20000000000000 : ℝ)^823
        have hw : |(1037968111/2500000000 : ℝ)|=(1037968111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1356_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77640267/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3679/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11181/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5591/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2943/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3679/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11181/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3679/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11181/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3679/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11181/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3679/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11181/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3679/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11181/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3679/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11181/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11181/100000 : ℝ) ^ (4315/1024 : ℝ) ≤ (1956382718092543/20000000000000000000 : ℝ) := by
    have hpowers : (11181/100000 : ℝ)^4315 ≤ (1956382718092543/20000000000000000000 : ℝ)^1024 := by
      have hnat : (11181 : ℕ)^4315*20000000000000000000^1024 ≤ 1956382718092543^1024*100000^4315 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11181 100000 1956382718092543 20000000000000000000 4315 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11181/100000 : ℝ)) (X := (1956382718092543/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4315 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3679/25000 : ℝ) ^ (4315/1024 : ℝ) ≤ (31129823426276911/100000000000000000000 : ℝ) := by
    have hpowers : (3679/25000 : ℝ)^4315 ≤ (31129823426276911/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3679 : ℕ)^4315*100000000000000000000^1024 ≤ 31129823426276911^1024*25000^4315 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3679 25000 31129823426276911 100000000000000000000 4315 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3679/25000 : ℝ)) (X := (31129823426276911/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4315 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001956382718092543/10000000000000000000 : ℝ) ≤ (10000464237881949/10000000000000000 : ℝ) ^ (4315/1024 : ℝ) := by
    have hpowers : (10001956382718092543/10000000000000000000 : ℝ)^1024 ≤ (10000464237881949/10000000000000000 : ℝ)^4315 := by
      have hnat : (10001956382718092543 : ℕ)^1024*10000000000000000^4315 ≤ 10000464237881949^4315*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001956382718092543 10000000000000000000 10000464237881949 10000000000000000 1024 4315 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000464237881949/10000000000000000 : ℝ)) (X := (10001956382718092543/10000000000000000000 : ℝ)) (by norm_num) 4315 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020455868508369813/50000000000000000000 : ℝ) ≤ (5000485365982193/5000000000000000 : ℝ) ^ (4315/1024 : ℝ) := by
    have hpowers : (50020455868508369813/50000000000000000000 : ℝ)^1024 ≤ (5000485365982193/5000000000000000 : ℝ)^4315 := by
      have hnat : (50020455868508369813 : ℕ)^1024*5000000000000000^4315 ≤ 5000485365982193^4315*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020455868508369813 50000000000000000000 5000485365982193 5000000000000000 1024 4315 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000485365982193/5000000000000000 : ℝ)) (X := (50020455868508369813/50000000000000000000 : ℝ)) (by norm_num) 4315 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031129823426276911/50000000000000000000 : ℝ) ≤ (10001477226046823/10000000000000000 : ℝ) ^ (4315/1024 : ℝ) := by
    have hpowers : (50031129823426276911/50000000000000000000 : ℝ)^1024 ≤ (10001477226046823/10000000000000000 : ℝ)^4315 := by
      have hnat : (50031129823426276911 : ℕ)^1024*10000000000000000^4315 ≤ 10001477226046823^4315*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031129823426276911 50000000000000000000 10001477226046823 10000000000000000 1024 4315 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001477226046823/10000000000000000 : ℝ)) (X := (50031129823426276911/50000000000000000000 : ℝ)) (by norm_num) 4315 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1956382718092543/20000000000000000000 : ℝ) ≤ ((5048616408605890503/5050000000000000000 : ℝ)+2*(72356297491/50500000000000 : ℝ)*(11181/100000 : ℝ))^(4315/1024 : ℝ) := by
    rw [show (5048616408605890503/5050000000000000000 : ℝ)+2*(72356297491/50500000000000 : ℝ)*(11181/100000 : ℝ)=(10000464237881949/10000000000000000 : ℝ) by norm_num, show 1+2*(1956382718092543/20000000000000000000 : ℝ)=(10001956382718092543/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31129823426276911/100000000000000000000 : ℝ)+(1956382718092543/20000000000000000000 : ℝ) ≤ ((5048616408605890503/5050000000000000000 : ℝ)+(72356297491/50500000000000 : ℝ)*((3679/25000 : ℝ)+(11181/100000 : ℝ)))^(4315/1024 : ℝ) := by
    rw [show (5048616408605890503/5050000000000000000 : ℝ)+(72356297491/50500000000000 : ℝ)*((3679/25000 : ℝ)+(11181/100000 : ℝ))=(5000485365982193/5000000000000000 : ℝ) by norm_num, show 1+(31129823426276911/100000000000000000000 : ℝ)+(1956382718092543/20000000000000000000 : ℝ)=(50020455868508369813/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31129823426276911/100000000000000000000 : ℝ) ≤ ((5048616408605890503/5050000000000000000 : ℝ)+2*(72356297491/50500000000000 : ℝ)*(3679/25000 : ℝ))^(4315/1024 : ℝ) := by
    rw [show (5048616408605890503/5050000000000000000 : ℝ)+2*(72356297491/50500000000000 : ℝ)*(3679/25000 : ℝ)=(10001477226046823/10000000000000000 : ℝ) by norm_num, show 1+2*(31129823426276911/100000000000000000000 : ℝ)=(50031129823426276911/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5048616408605890503/5050000000000000000 : ℝ)*(X 1 0+X 2 0)+(72356297491/50500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4315/1024 : ℝ)) (lo := (11181/100000 : ℝ)) (hi := (3679/25000 : ℝ)) (c := (5048616408605890503/5050000000000000000 : ℝ)) (alpha := (72356297491/50500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5048616408605890503/5050000000000000000 : ℝ)*(X 0 1+X 2 1)+(72356297491/50500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4315/1024 : ℝ)) (lo := (11181/100000 : ℝ)) (hi := (3679/25000 : ℝ)) (c := (5048616408605890503/5050000000000000000 : ℝ)) (alpha := (72356297491/50500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5048616408605890503/5050000000000000000 : ℝ)*(X 0 2+X 1 2)+(72356297491/50500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4315/1024 : ℝ)) (lo := (11181/100000 : ℝ)) (hi := (3679/25000 : ℝ)) (c := (5048616408605890503/5050000000000000000 : ℝ)) (alpha := (72356297491/50500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2031941329/10000000000 : ℝ)*X 0 0+(5411940797/10000000000 : ℝ)*X 0 1+(2622534839/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069748183/2000000000 : ℝ)*X 1 0+(-4134671/19531250 : ℝ)*X 1 1+(2622534837/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668592617/1250000000 : ℝ)*X 2 0+(1049013933/2000000000 : ℝ)*X 2 1+(-2116951537/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4322974489/10000000000 : ℝ)*X 0 0+(4150607263/10000000000 : ℝ)*X 0 1+(1125493219/2500000000 : ℝ)*X 0 2+(4322974489/10000000000 : ℝ)*X 1 0+(4150607263/10000000000 : ℝ)*X 1 1+(1125493219/2500000000 : ℝ)*X 1 2+(4322974489/10000000000 : ℝ)*X 2 0+(4150607263/10000000000 : ℝ)*X 2 1+(1125493219/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2031953489/10000000000 : ℝ)*X 0 0+(5245667371/10000000000 : ℝ)*X 0 1+(676417489/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652845141/5000000000 : ℝ)*X 1 0+(-1950681207/10000000000 : ℝ)*X 1 1+(5411339829/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652845139/5000000000 : ℝ)*X 2 0+(338208737/625000000 : ℝ)*X 2 1+(-121917579/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((172919991/400000000 : ℝ)*X 0 0+(4500714193/10000000000 : ℝ)*X 0 1+(1037968111/2500000000 : ℝ)*X 0 2+(172919991/400000000 : ℝ)*X 1 0+(4500714193/10000000000 : ℝ)*X 1 1+(1037968111/2500000000 : ℝ)*X 1 2+(172919991/400000000 : ℝ)*X 2 0+(4500714193/10000000000 : ℝ)*X 2 1+(1037968111/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1115295615127126829220045303/126250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1631448021/100000000000000 : ℝ)*(base19) + (1543776857/100000000000000 : ℝ)*(base23) + (59477737/100000000000000 : ℝ)*(lower2) + (105481501/50000000000000 : ℝ)*(upper3) + (6093379/4000000000000 : ℝ)*(upper5) + (4419393974383867/100000000000000 : ℝ)*(major0) + (4419393974383867/100000000000000 : ℝ)*(major1) + (4419393974383867/100000000000000 : ℝ)*(major2) + (5992683006370567/100000000000000 : ℝ)*(sp0) + (1198543039659873/20000000000000 : ℝ)*(sp1) + (187272352686579/3125000000000 : ℝ)*(sp2) + (711513453651211/25000000000000 : ℝ)*(sp3) + (33823376819/100000000000000 : ℝ)*(sp4) + (8504974003/50000000000000 : ℝ)*(sp7) + (56921416491057/2000000000000 : ℝ)*(f.failure) + (2996358414873693/50000000000000 : ℝ)*(f.sum) + (9697804939397/2525000000000000000000000000 : ℝ)*base65 + (3821007924328584899/505000000000000000000000000000000 : ℝ)*base68 + (4480790163748584899/505000000000000000000000000000000 : ℝ)*base70 + (5959186238143584899/505000000000000000000000000000000 : ℝ)*base72 + (12668590313553/2525000000000000000000000000 : ℝ)*base74 + (6834741440028584899/505000000000000000000000000000000 : ℝ)*base76 + (298210569191415101/505000000000000000000000000000000 : ℝ)*base77 + (2600644302188584899/505000000000000000000000000000000 : ℝ)*base80 + (15859659614103/2525000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1592219/100000000000000000000 : ℝ)*base89 + (1592219/100000000000000000000 : ℝ)*base91 + (1592219/100000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (281942481079966058874563949/63125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1350840543/100000000000000 : ℝ)*(base19) + (145486819/10000000000000 : ℝ)*(base23) + (218090029/50000000000000 : ℝ)*(lower1) + (613321/1000000000000 : ℝ)*(upper2) + (59596927/50000000000000 : ℝ)*(upper3) + (155575879/100000000000000 : ℝ)*(upper5) + (1112824089053613/25000000000000 : ℝ)*(major0) + (1112824089053613/25000000000000 : ℝ)*(major1) + (1112824089053613/25000000000000 : ℝ)*(major2) + (27031123/3125000000000 : ℝ)*(sp1) + (3017988370747023/50000000000000 : ℝ)*(sp4) + (6035974525657567/100000000000000 : ℝ)*(sp5) + (94312113853529/1562500000000 : ℝ)*(sp6) + (2866615822054329/100000000000000 : ℝ)*(sp7) + (2866615822054329/100000000000000 : ℝ)*(f.failure) + (3017988370747023/50000000000000 : ℝ)*(f.sum) + (378073100407/2525000000000000000000000000 : ℝ)*base65 + (1148773926794087339/126250000000000000000000000000000 : ℝ)*base67 + (1880290481837837339/126250000000000000000000000000000 : ℝ)*base69 + (1362869087611587339/126250000000000000000000000000000 : ℝ)*base71 + (74377628383/631250000000000000000000000 : ℝ)*base73 + (1988989591269087339/126250000000000000000000000000000 : ℝ)*base75 + (1297339955069087339/126250000000000000000000000000000 : ℝ)*base77 + (2272917954936587339/126250000000000000000000000000000 : ℝ)*base79 + (3528177243273/157812500000000000000000000 : ℝ)*base82 + (7934157/5000000000000000000000 : ℝ)*base90 + (7934157/5000000000000000000000 : ℝ)*base92 + (7934157/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1356_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77640267/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3679/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11181/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5591/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2943/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1356_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1356_box_0 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-116611773/625000000 : ℝ)*x 0 + (5389354013/10000000000 : ℝ)*x 1 + (5389354689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (116611773/625000000 : ℝ)^1079 ≤ (11067739841593/100000000000000 : ℝ)^823 := by
    have hnat : (116611773 : ℕ)^1079*100000000000000^823 ≤ 11067739841593^823*625000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116611773 625000000 11067739841593 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5389354013/10000000000 : ℝ)^1079 ≤ (22233063206101/50000000000000 : ℝ)^823 := by
    have hnat : (5389354013 : ℕ)^1079*50000000000000^823 ≤ 22233063206101^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389354013 10000000000 22233063206101 50000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5389354689/10000000000 : ℝ)^1079 ≤ (22233066862309/50000000000000 : ℝ)^823 := by
    have hnat : (5389354689 : ℕ)^1079*50000000000000^823 ≤ 22233066862309^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389354689 10000000000 22233066862309 50000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-116611773/625000000 : ℝ), (5389354013/10000000000 : ℝ), (5389354689/10000000000 : ℝ)] ![(11067739841593/100000000000000 : ℝ), (22233063206101/50000000000000 : ℝ), (22233066862309/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-116611773/625000000 : ℝ)|^1079 ≤ (11067739841593/100000000000000 : ℝ)^823
        have hw : |(-116611773/625000000 : ℝ)|=(116611773/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5389354013/10000000000 : ℝ)|^1079 ≤ (22233063206101/50000000000000 : ℝ)^823
        have hw : |(5389354013/10000000000 : ℝ)|=(5389354013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5389354689/10000000000 : ℝ)|^1079 ≤ (22233066862309/50000000000000 : ℝ)^823
        have hw : |(5389354689/10000000000 : ℝ)|=(5389354689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_box_1 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5285348697/10000000000 : ℝ)*x 0 + (-40166979/200000000 : ℝ)*x 1 + (5389353967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285348697/10000000000 : ℝ)^1079 ≤ (43344473664577/100000000000000 : ℝ)^823 := by
    have hnat : (5285348697 : ℕ)^1079*100000000000000^823 ≤ 43344473664577^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285348697 10000000000 43344473664577 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40166979/200000000 : ℝ)^1079 ≤ (2437880079439/20000000000000 : ℝ)^823 := by
    have hnat : (40166979 : ℕ)^1079*20000000000000^823 ≤ 2437880079439^823*200000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40166979 200000000 2437880079439 20000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5389353967/10000000000 : ℝ)^1079 ≤ (44466125914611/100000000000000 : ℝ)^823 := by
    have hnat : (5389353967 : ℕ)^1079*100000000000000^823 ≤ 44466125914611^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389353967 10000000000 44466125914611 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285348697/10000000000 : ℝ), (-40166979/200000000 : ℝ), (5389353967/10000000000 : ℝ)] ![(43344473664577/100000000000000 : ℝ), (2437880079439/20000000000000 : ℝ), (44466125914611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285348697/10000000000 : ℝ)|^1079 ≤ (43344473664577/100000000000000 : ℝ)^823
        have hw : |(5285348697/10000000000 : ℝ)|=(5285348697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-40166979/200000000 : ℝ)|^1079 ≤ (2437880079439/20000000000000 : ℝ)^823
        have hw : |(-40166979/200000000 : ℝ)|=(40166979/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5389353967/10000000000 : ℝ)|^1079 ≤ (44466125914611/100000000000000 : ℝ)^823
        have hw : |(5389353967/10000000000 : ℝ)|=(5389353967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_box_2 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1321337127/2500000000 : ℝ)*x 0 + (1347338541/2500000000 : ℝ)*x 1 + (-1004174469/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321337127/2500000000 : ℝ)^1079 ≤ (10836117908121/25000000000000 : ℝ)^823 := by
    have hnat : (1321337127 : ℕ)^1079*25000000000000^823 ≤ 10836117908121^823*2500000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321337127 2500000000 10836117908121 25000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347338541/2500000000 : ℝ)^1079 ≤ (44466128045597/100000000000000 : ℝ)^823 := by
    have hnat : (1347338541 : ℕ)^1079*100000000000000^823 ≤ 44466128045597^823*2500000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347338541 2500000000 44466128045597 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1004174469/5000000000 : ℝ)^1079 ≤ (3047350075427/25000000000000 : ℝ)^823 := by
    have hnat : (1004174469 : ℕ)^1079*25000000000000^823 ≤ 3047350075427^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004174469 5000000000 3047350075427 25000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321337127/2500000000 : ℝ), (1347338541/2500000000 : ℝ), (-1004174469/5000000000 : ℝ)] ![(10836117908121/25000000000000 : ℝ), (44466128045597/100000000000000 : ℝ), (3047350075427/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321337127/2500000000 : ℝ)|^1079 ≤ (10836117908121/25000000000000 : ℝ)^823
        have hw : |(1321337127/2500000000 : ℝ)|=(1321337127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347338541/2500000000 : ℝ)|^1079 ≤ (44466128045597/100000000000000 : ℝ)^823
        have hw : |(1347338541/2500000000 : ℝ)|=(1347338541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1004174469/5000000000 : ℝ)|^1079 ≤ (3047350075427/25000000000000 : ℝ)^823
        have hw : |(-1004174469/5000000000 : ℝ)|=(1004174469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_box_3 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1117710169/2500000000 : ℝ)*x 0 + (2126449827/5000000000 : ℝ)*x 1 + (4252899923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1117710169/2500000000 : ℝ)^1079 ≤ (34804890124637/100000000000000 : ℝ)^823 := by
    have hnat : (1117710169 : ℕ)^1079*100000000000000^823 ≤ 34804890124637^823*2500000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1117710169 2500000000 34804890124637 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2126449827/5000000000 : ℝ)^1079 ≤ (3259755358441/10000000000000 : ℝ)^823 := by
    have hnat : (2126449827 : ℕ)^1079*10000000000000^823 ≤ 3259755358441^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126449827 5000000000 3259755358441 10000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4252899923/10000000000 : ℝ)^1079 ≤ (32597556287583/100000000000000 : ℝ)^823 := by
    have hnat : (4252899923 : ℕ)^1079*100000000000000^823 ≤ 32597556287583^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4252899923 10000000000 32597556287583 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1117710169/2500000000 : ℝ), (2126449827/5000000000 : ℝ), (4252899923/10000000000 : ℝ)] ![(34804890124637/100000000000000 : ℝ), (3259755358441/10000000000000 : ℝ), (32597556287583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1117710169/2500000000 : ℝ)|^1079 ≤ (34804890124637/100000000000000 : ℝ)^823
        have hw : |(1117710169/2500000000 : ℝ)|=(1117710169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2126449827/5000000000 : ℝ)|^1079 ≤ (3259755358441/10000000000000 : ℝ)^823
        have hw : |(2126449827/5000000000 : ℝ)|=(2126449827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4252899923/10000000000 : ℝ)|^1079 ≤ (32597556287583/100000000000000 : ℝ)^823
        have hw : |(4252899923/10000000000 : ℝ)|=(4252899923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_box_4 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-550210689/2500000000 : ℝ)*x 0 + (5265227589/10000000000 : ℝ)*x 1 + (5265227117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (550210689/2500000000 : ℝ)^1079 ≤ (13743478094113/100000000000000 : ℝ)^823 := by
    have hnat : (550210689 : ℕ)^1079*100000000000000^823 ≤ 13743478094113^823*2500000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550210689 2500000000 13743478094113 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265227589/10000000000 : ℝ)^1079 ≤ (21564131740097/50000000000000 : ℝ)^823 := by
    have hnat : (5265227589 : ℕ)^1079*50000000000000^823 ≤ 21564131740097^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265227589 10000000000 21564131740097 50000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265227117/10000000000 : ℝ)^1079 ≤ (10782064602839/25000000000000 : ℝ)^823 := by
    have hnat : (5265227117 : ℕ)^1079*25000000000000^823 ≤ 10782064602839^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265227117 10000000000 10782064602839 25000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-550210689/2500000000 : ℝ), (5265227589/10000000000 : ℝ), (5265227117/10000000000 : ℝ)] ![(13743478094113/100000000000000 : ℝ), (21564131740097/50000000000000 : ℝ), (10782064602839/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-550210689/2500000000 : ℝ)|^1079 ≤ (13743478094113/100000000000000 : ℝ)^823
        have hw : |(-550210689/2500000000 : ℝ)|=(550210689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265227589/10000000000 : ℝ)|^1079 ≤ (21564131740097/50000000000000 : ℝ)^823
        have hw : |(5265227589/10000000000 : ℝ)|=(5265227589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265227117/10000000000 : ℝ)|^1079 ≤ (10782064602839/25000000000000 : ℝ)^823
        have hw : |(5265227117/10000000000 : ℝ)|=(5265227117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_box_5 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5372481007/10000000000 : ℝ)*x 0 + (-2058254391/10000000000 : ℝ)*x 1 + (131630693/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5372481007/10000000000 : ℝ)^1079 ≤ (11070924237067/25000000000000 : ℝ)^823 := by
    have hnat : (5372481007 : ℕ)^1079*25000000000000^823 ≤ 11070924237067^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5372481007 10000000000 11070924237067 25000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2058254391/10000000000 : ℝ)^1079 ≤ (2517607630537/20000000000000 : ℝ)^823 := by
    have hnat : (2058254391 : ℕ)^1079*20000000000000^823 ≤ 2517607630537^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2058254391 10000000000 2517607630537 20000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131630693/250000000 : ℝ)^1079 ≤ (10782066221753/25000000000000 : ℝ)^823 := by
    have hnat : (131630693 : ℕ)^1079*25000000000000^823 ≤ 10782066221753^823*250000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131630693 250000000 10782066221753 25000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5372481007/10000000000 : ℝ), (-2058254391/10000000000 : ℝ), (131630693/250000000 : ℝ)] ![(11070924237067/25000000000000 : ℝ), (2517607630537/20000000000000 : ℝ), (10782066221753/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5372481007/10000000000 : ℝ)|^1079 ≤ (11070924237067/25000000000000 : ℝ)^823
        have hw : |(5372481007/10000000000 : ℝ)|=(5372481007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2058254391/10000000000 : ℝ)|^1079 ≤ (2517607630537/20000000000000 : ℝ)^823
        have hw : |(-2058254391/10000000000 : ℝ)|=(2058254391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131630693/250000000 : ℝ)|^1079 ≤ (10782066221753/25000000000000 : ℝ)^823
        have hw : |(131630693/250000000 : ℝ)|=(131630693/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_box_6 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5372481491/10000000000 : ℝ)*x 0 + (263261363/500000000 : ℝ)*x 1 + (-1029127177/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5372481491/10000000000 : ℝ)^1079 ≤ (1107092554467/2500000000000 : ℝ)^823 := by
    have hnat : (5372481491 : ℕ)^1079*2500000000000^823 ≤ 1107092554467^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5372481491 10000000000 1107092554467 2500000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263261363/500000000 : ℝ)^1079 ≤ (21564129973521/50000000000000 : ℝ)^823 := by
    have hnat : (263261363 : ℕ)^1079*50000000000000^823 ≤ 21564129973521^823*500000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263261363 500000000 21564129973521 50000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1029127177/5000000000 : ℝ)^1079 ≤ (12588037856009/100000000000000 : ℝ)^823 := by
    have hnat : (1029127177 : ℕ)^1079*100000000000000^823 ≤ 12588037856009^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029127177 5000000000 12588037856009 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5372481491/10000000000 : ℝ), (263261363/500000000 : ℝ), (-1029127177/5000000000 : ℝ)] ![(1107092554467/2500000000000 : ℝ), (21564129973521/50000000000000 : ℝ), (12588037856009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5372481491/10000000000 : ℝ)|^1079 ≤ (1107092554467/2500000000000 : ℝ)^823
        have hw : |(5372481491/10000000000 : ℝ)|=(5372481491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263261363/500000000 : ℝ)|^1079 ≤ (21564129973521/50000000000000 : ℝ)^823
        have hw : |(263261363/500000000 : ℝ)|=(263261363/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1029127177/5000000000 : ℝ)|^1079 ≤ (12588037856009/100000000000000 : ℝ)^823
        have hw : |(-1029127177/5000000000 : ℝ)|=(1029127177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_box_7 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4174162011/10000000000 : ℝ)*x 0 + (2200592931/5000000000 : ℝ)*x 1 + (1100296529/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4174162011/10000000000 : ℝ)^1079 ≤ (7952152390303/25000000000000 : ℝ)^823 := by
    have hnat : (4174162011 : ℕ)^1079*25000000000000^823 ≤ 7952152390303^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4174162011 10000000000 7952152390303 25000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2200592931/5000000000 : ℝ)^1079 ≤ (34095693919953/100000000000000 : ℝ)^823 := by
    have hnat : (2200592931 : ℕ)^1079*100000000000000^823 ≤ 34095693919953^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200592931 5000000000 34095693919953 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1100296529/2500000000 : ℝ)^1079 ≤ (34095696499747/100000000000000 : ℝ)^823 := by
    have hnat : (1100296529 : ℕ)^1079*100000000000000^823 ≤ 34095696499747^823*2500000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100296529 2500000000 34095696499747 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4174162011/10000000000 : ℝ), (2200592931/5000000000 : ℝ), (1100296529/2500000000 : ℝ)] ![(7952152390303/25000000000000 : ℝ), (34095693919953/100000000000000 : ℝ), (34095696499747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4174162011/10000000000 : ℝ)|^1079 ≤ (7952152390303/25000000000000 : ℝ)^823
        have hw : |(4174162011/10000000000 : ℝ)|=(4174162011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2200592931/5000000000 : ℝ)|^1079 ≤ (34095693919953/100000000000000 : ℝ)^823
        have hw : |(2200592931/5000000000 : ℝ)|=(2200592931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1100296529/2500000000 : ℝ)|^1079 ≤ (34095696499747/100000000000000 : ℝ)^823
        have hw : |(1100296529/2500000000 : ℝ)|=(1100296529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_box_8 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2130445299/10000000000 : ℝ)*x 0 + (2589854399/5000000000 : ℝ)*x 1 + (5403368301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2130445299/10000000000 : ℝ)^1079 ≤ (13170016788993/100000000000000 : ℝ)^823 := by
    have hnat : (2130445299 : ℕ)^1079*100000000000000^823 ≤ 13170016788993^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130445299 10000000000 13170016788993 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2589854399/5000000000 : ℝ)^1079 ≤ (42212200388987/100000000000000 : ℝ)^823 := by
    have hnat : (2589854399 : ℕ)^1079*100000000000000^823 ≤ 42212200388987^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589854399 5000000000 42212200388987 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5403368301/10000000000 : ℝ)^1079 ≤ (11154445702449/25000000000000 : ℝ)^823 := by
    have hnat : (5403368301 : ℕ)^1079*25000000000000^823 ≤ 11154445702449^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403368301 10000000000 11154445702449 25000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2130445299/10000000000 : ℝ), (2589854399/5000000000 : ℝ), (5403368301/10000000000 : ℝ)] ![(13170016788993/100000000000000 : ℝ), (42212200388987/100000000000000 : ℝ), (11154445702449/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2130445299/10000000000 : ℝ)|^1079 ≤ (13170016788993/100000000000000 : ℝ)^823
        have hw : |(-2130445299/10000000000 : ℝ)|=(2130445299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2589854399/5000000000 : ℝ)|^1079 ≤ (42212200388987/100000000000000 : ℝ)^823
        have hw : |(2589854399/5000000000 : ℝ)|=(2589854399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5403368301/10000000000 : ℝ)|^1079 ≤ (11154445702449/25000000000000 : ℝ)^823
        have hw : |(5403368301/10000000000 : ℝ)|=(5403368301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_box_9 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2637753077/5000000000 : ℝ)*x 0 + (-2002583423/10000000000 : ℝ)*x 1 + (1080673569/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637753077/5000000000 : ℝ)^1079 ≤ (43238679147073/100000000000000 : ℝ)^823 := by
    have hnat : (2637753077 : ℕ)^1079*100000000000000^823 ≤ 43238679147073^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637753077 5000000000 43238679147073 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2002583423/10000000000 : ℝ)^1079 ≤ (2428708593467/20000000000000 : ℝ)^823 := by
    have hnat : (2002583423 : ℕ)^1079*20000000000000^823 ≤ 2428708593467^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2002583423 10000000000 2428708593467 20000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080673569/2000000000 : ℝ)^1079 ≤ (22308888936587/50000000000000 : ℝ)^823 := by
    have hnat : (1080673569 : ℕ)^1079*50000000000000^823 ≤ 22308888936587^823*2000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080673569 2000000000 22308888936587 50000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637753077/5000000000 : ℝ), (-2002583423/10000000000 : ℝ), (1080673569/2000000000 : ℝ)] ![(43238679147073/100000000000000 : ℝ), (2428708593467/20000000000000 : ℝ), (22308888936587/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637753077/5000000000 : ℝ)|^1079 ≤ (43238679147073/100000000000000 : ℝ)^823
        have hw : |(2637753077/5000000000 : ℝ)|=(2637753077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2002583423/10000000000 : ℝ)|^1079 ≤ (2428708593467/20000000000000 : ℝ)^823
        have hw : |(-2002583423/10000000000 : ℝ)|=(2002583423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080673569/2000000000 : ℝ)|^1079 ≤ (22308888936587/50000000000000 : ℝ)^823
        have hw : |(1080673569/2000000000 : ℝ)|=(1080673569/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_box_10 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5275505739/10000000000 : ℝ)*x 0 + (216134731/400000000 : ℝ)*x 1 + (-1001291699/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275505739/10000000000 : ℝ)^1079 ≤ (43238674687657/100000000000000 : ℝ)^823 := by
    have hnat : (5275505739 : ℕ)^1079*100000000000000^823 ≤ 43238674687657^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275505739 10000000000 43238674687657 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216134731/400000000 : ℝ)^1079 ≤ (22308891264161/50000000000000 : ℝ)^823 := by
    have hnat : (216134731 : ℕ)^1079*50000000000000^823 ≤ 22308891264161^823*400000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216134731 400000000 22308891264161 50000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1001291699/5000000000 : ℝ)^1079 ≤ (12143542768581/100000000000000 : ℝ)^823 := by
    have hnat : (1001291699 : ℕ)^1079*100000000000000^823 ≤ 12143542768581^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001291699 5000000000 12143542768581 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275505739/10000000000 : ℝ), (216134731/400000000 : ℝ), (-1001291699/5000000000 : ℝ)] ![(43238674687657/100000000000000 : ℝ), (22308891264161/50000000000000 : ℝ), (12143542768581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275505739/10000000000 : ℝ)|^1079 ≤ (43238674687657/100000000000000 : ℝ)^823
        have hw : |(5275505739/10000000000 : ℝ)|=(5275505739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216134731/400000000 : ℝ)|^1079 ≤ (22308891264161/50000000000000 : ℝ)^823
        have hw : |(216134731/400000000 : ℝ)|=(216134731/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1001291699/5000000000 : ℝ)|^1079 ≤ (12143542768581/100000000000000 : ℝ)^823
        have hw : |(-1001291699/5000000000 : ℝ)|=(1001291699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_box_11 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2251888059/5000000000 : ℝ)*x 0 + (169445773/400000000 : ℝ)*x 1 + (4236145007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2251888059/5000000000 : ℝ)^1079 ≤ (17570713494057/50000000000000 : ℝ)^823 := by
    have hnat : (2251888059 : ℕ)^1079*50000000000000^823 ≤ 17570713494057^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251888059 5000000000 17570713494057 50000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169445773/400000000 : ℝ)^1079 ≤ (8107320768901/25000000000000 : ℝ)^823 := by
    have hnat : (169445773 : ℕ)^1079*25000000000000^823 ≤ 8107320768901^823*400000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169445773 400000000 8107320768901 25000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4236145007/10000000000 : ℝ)^1079 ≤ (3242928992059/10000000000000 : ℝ)^823 := by
    have hnat : (4236145007 : ℕ)^1079*10000000000000^823 ≤ 3242928992059^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4236145007 10000000000 3242928992059 10000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2251888059/5000000000 : ℝ), (169445773/400000000 : ℝ), (4236145007/10000000000 : ℝ)] ![(17570713494057/50000000000000 : ℝ), (8107320768901/25000000000000 : ℝ), (3242928992059/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2251888059/5000000000 : ℝ)|^1079 ≤ (17570713494057/50000000000000 : ℝ)^823
        have hw : |(2251888059/5000000000 : ℝ)|=(2251888059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169445773/400000000 : ℝ)|^1079 ≤ (8107320768901/25000000000000 : ℝ)^823
        have hw : |(169445773/400000000 : ℝ)|=(169445773/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4236145007/10000000000 : ℝ)|^1079 ≤ (3242928992059/10000000000000 : ℝ)^823
        have hw : |(4236145007/10000000000 : ℝ)|=(4236145007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_box_12 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-968247897/5000000000 : ℝ)*x 0 + (547269869/1000000000 : ℝ)*x 1 + (5254146843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (968247897/5000000000 : ℝ)^1079 ≤ (11620852542659/100000000000000 : ℝ)^823 := by
    have hnat : (968247897 : ℕ)^1079*100000000000000^823 ≤ 11620852542659^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      968247897 5000000000 11620852542659 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (547269869/1000000000 : ℝ)^1079 ≤ (45369841842581/100000000000000 : ℝ)^823 := by
    have hnat : (547269869 : ℕ)^1079*100000000000000^823 ≤ 45369841842581^823*1000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547269869 1000000000 45369841842581 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254146843/10000000000 : ℝ)^1079 ≤ (43009305606947/100000000000000 : ℝ)^823 := by
    have hnat : (5254146843 : ℕ)^1079*100000000000000^823 ≤ 43009305606947^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254146843 10000000000 43009305606947 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-968247897/5000000000 : ℝ), (547269869/1000000000 : ℝ), (5254146843/10000000000 : ℝ)] ![(11620852542659/100000000000000 : ℝ), (45369841842581/100000000000000 : ℝ), (43009305606947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-968247897/5000000000 : ℝ)|^1079 ≤ (11620852542659/100000000000000 : ℝ)^823
        have hw : |(-968247897/5000000000 : ℝ)|=(968247897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(547269869/1000000000 : ℝ)|^1079 ≤ (45369841842581/100000000000000 : ℝ)^823
        have hw : |(547269869/1000000000 : ℝ)|=(547269869/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254146843/10000000000 : ℝ)|^1079 ≤ (43009305606947/100000000000000 : ℝ)^823
        have hw : |(5254146843/10000000000 : ℝ)|=(5254146843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_box_13 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2690128763/5000000000 : ℝ)*x 0 + (-1031303113/5000000000 : ℝ)*x 1 + (1050829307/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2690128763/5000000000 : ℝ)^1079 ≤ (44367753884107/100000000000000 : ℝ)^823 := by
    have hnat : (2690128763 : ℕ)^1079*100000000000000^823 ≤ 44367753884107^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690128763 5000000000 44367753884107 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1031303113/5000000000 : ℝ)^1079 ≤ (12622943804351/100000000000000 : ℝ)^823 := by
    have hnat : (1031303113 : ℕ)^1079*100000000000000^823 ≤ 12622943804351^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031303113 5000000000 12622943804351 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1050829307/2000000000 : ℝ)^1079 ≤ (21504651150741/50000000000000 : ℝ)^823 := by
    have hnat : (1050829307 : ℕ)^1079*50000000000000^823 ≤ 21504651150741^823*2000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050829307 2000000000 21504651150741 50000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2690128763/5000000000 : ℝ), (-1031303113/5000000000 : ℝ), (1050829307/2000000000 : ℝ)] ![(44367753884107/100000000000000 : ℝ), (12622943804351/100000000000000 : ℝ), (21504651150741/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2690128763/5000000000 : ℝ)|^1079 ≤ (44367753884107/100000000000000 : ℝ)^823
        have hw : |(2690128763/5000000000 : ℝ)|=(2690128763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1031303113/5000000000 : ℝ)|^1079 ≤ (12622943804351/100000000000000 : ℝ)^823
        have hw : |(-1031303113/5000000000 : ℝ)|=(1031303113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1050829307/2000000000 : ℝ)|^1079 ≤ (21504651150741/50000000000000 : ℝ)^823
        have hw : |(1050829307/2000000000 : ℝ)|=(1050829307/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_box_14 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2690128651/5000000000 : ℝ)*x 0 + (41048023/78125000 : ℝ)*x 1 + (-2062605981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2690128651/5000000000 : ℝ)^1079 ≤ (44367751462331/100000000000000 : ℝ)^823 := by
    have hnat : (2690128651 : ℕ)^1079*100000000000000^823 ≤ 44367751462331^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690128651 5000000000 44367751462331 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41048023/78125000 : ℝ)^1079 ≤ (21504653345441/50000000000000 : ℝ)^823 := by
    have hnat : (41048023 : ℕ)^1079*50000000000000^823 ≤ 21504653345441^823*78125000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41048023 78125000 21504653345441 50000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2062605981/10000000000 : ℝ)^1079 ≤ (1577867729823/12500000000000 : ℝ)^823 := by
    have hnat : (2062605981 : ℕ)^1079*12500000000000^823 ≤ 1577867729823^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062605981 10000000000 1577867729823 12500000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2690128651/5000000000 : ℝ), (41048023/78125000 : ℝ), (-2062605981/10000000000 : ℝ)] ![(44367751462331/100000000000000 : ℝ), (21504653345441/50000000000000 : ℝ), (1577867729823/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2690128651/5000000000 : ℝ)|^1079 ≤ (44367751462331/100000000000000 : ℝ)^823
        have hw : |(2690128651/5000000000 : ℝ)|=(2690128651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41048023/78125000 : ℝ)|^1079 ≤ (21504653345441/50000000000000 : ℝ)^823
        have hw : |(41048023/78125000 : ℝ)|=(41048023/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2062605981/10000000000 : ℝ)|^1079 ≤ (1577867729823/12500000000000 : ℝ)^823
        have hw : |(-2062605981/10000000000 : ℝ)|=(2062605981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_box_15 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2592019/6250000 : ℝ)*x 0 + (110360309/250000000 : ℝ)*x 1 + (2207206111/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2592019/6250000 : ℝ)^1079 ≤ (15769906824653/50000000000000 : ℝ)^823 := by
    have hnat : (2592019 : ℕ)^1079*50000000000000^823 ≤ 15769906824653^823*6250000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592019 6250000 15769906824653 50000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (110360309/250000000 : ℝ)^1079 ≤ (34230093869267/100000000000000 : ℝ)^823 := by
    have hnat : (110360309 : ℕ)^1079*100000000000000^823 ≤ 34230093869267^823*250000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110360309 250000000 34230093869267 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2207206111/5000000000 : ℝ)^1079 ≤ (34230092466337/100000000000000 : ℝ)^823 := by
    have hnat : (2207206111 : ℕ)^1079*100000000000000^823 ≤ 34230092466337^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207206111 5000000000 34230092466337 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2592019/6250000 : ℝ), (110360309/250000000 : ℝ), (2207206111/5000000000 : ℝ)] ![(15769906824653/50000000000000 : ℝ), (34230093869267/100000000000000 : ℝ), (34230092466337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2592019/6250000 : ℝ)|^1079 ≤ (15769906824653/50000000000000 : ℝ)^823
        have hw : |(2592019/6250000 : ℝ)|=(2592019/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(110360309/250000000 : ℝ)|^1079 ≤ (34230093869267/100000000000000 : ℝ)^823
        have hw : |(110360309/250000000 : ℝ)|=(110360309/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2207206111/5000000000 : ℝ)|^1079 ≤ (34230092466337/100000000000000 : ℝ)^823
        have hw : |(2207206111/5000000000 : ℝ)|=(2207206111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1356_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77640267/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2943/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5591/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62861/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(7371/12500 : ℝ) ∧ (20009/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84407/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2943/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5591/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2943/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5591/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2943/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5591/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2943/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5591/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2943/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5591/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2943/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5591/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5591/50000 : ℝ) ^ (4315/1024 : ℝ) ≤ (1957120140670039/20000000000000000000 : ℝ) := by
    have hpowers : (5591/50000 : ℝ)^4315 ≤ (1957120140670039/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5591 : ℕ)^4315*20000000000000000000^1024 ≤ 1957120140670039^1024*50000^4315 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5591 50000 1957120140670039 20000000000000000000 4315 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5591/50000 : ℝ)) (X := (1957120140670039/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4315 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2943/20000 : ℝ) ^ (4315/1024 : ℝ) ≤ (31120910500334891/100000000000000000000 : ℝ) := by
    have hpowers : (2943/20000 : ℝ)^4315 ≤ (31120910500334891/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2943 : ℕ)^4315*100000000000000000000^1024 ≤ 31120910500334891^1024*20000^4315 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2943 20000 31120910500334891 100000000000000000000 4315 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2943/20000 : ℝ)) (X := (31120910500334891/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4315 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001957120140670039/10000000000000000000 : ℝ) ≤ (2000092882570969/2000000000000000 : ℝ) ^ (4315/1024 : ℝ) := by
    have hpowers : (10001957120140670039/10000000000000000000 : ℝ)^1024 ≤ (2000092882570969/2000000000000000 : ℝ)^4315 := by
      have hnat : (10001957120140670039 : ℕ)^1024*2000000000000000^4315 ≤ 2000092882570969^4315*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001957120140670039 10000000000000000000 2000092882570969 2000000000000000 1024 4315 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000092882570969/2000000000000000 : ℝ)) (X := (10001957120140670039/10000000000000000000 : ℝ)) (by norm_num) 4315 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020453255601842543/50000000000000000000 : ℝ) ≤ (5000485303994203/5000000000000000 : ℝ) ^ (4315/1024 : ℝ) := by
    have hpowers : (50020453255601842543/50000000000000000000 : ℝ)^1024 ≤ (5000485303994203/5000000000000000 : ℝ)^4315 := by
      have hnat : (50020453255601842543 : ℕ)^1024*5000000000000000^4315 ≤ 5000485303994203^4315*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020453255601842543 50000000000000000000 5000485303994203 5000000000000000 1024 4315 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000485303994203/5000000000000000 : ℝ)) (X := (50020453255601842543/50000000000000000000 : ℝ)) (by norm_num) 4315 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031120910500334891/50000000000000000000 : ℝ) ≤ (10001476803121967/10000000000000000 : ℝ) ^ (4315/1024 : ℝ) := by
    have hpowers : (50031120910500334891/50000000000000000000 : ℝ)^1024 ≤ (10001476803121967/10000000000000000 : ℝ)^4315 := by
      have hnat : (50031120910500334891 : ℕ)^1024*10000000000000000^4315 ≤ 10001476803121967^4315*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031120910500334891 50000000000000000000 10001476803121967 10000000000000000 1024 4315 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001476803121967/10000000000000000 : ℝ)) (X := (50031120910500334891/50000000000000000000 : ℝ)) (by norm_num) 4315 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1957120140670039/20000000000000000000 : ℝ) ≤ ((35320320222649209181/35330000000000000000 : ℝ)+2*(506195133561/353300000000000 : ℝ)*(5591/50000 : ℝ))^(4315/1024 : ℝ) := by
    rw [show (35320320222649209181/35330000000000000000 : ℝ)+2*(506195133561/353300000000000 : ℝ)*(5591/50000 : ℝ)=(2000092882570969/2000000000000000 : ℝ) by norm_num, show 1+2*(1957120140670039/20000000000000000000 : ℝ)=(10001957120140670039/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31120910500334891/100000000000000000000 : ℝ)+(1957120140670039/20000000000000000000 : ℝ) ≤ ((35320320222649209181/35330000000000000000 : ℝ)+(506195133561/353300000000000 : ℝ)*((2943/20000 : ℝ)+(5591/50000 : ℝ)))^(4315/1024 : ℝ) := by
    rw [show (35320320222649209181/35330000000000000000 : ℝ)+(506195133561/353300000000000 : ℝ)*((2943/20000 : ℝ)+(5591/50000 : ℝ))=(5000485303994203/5000000000000000 : ℝ) by norm_num, show 1+(31120910500334891/100000000000000000000 : ℝ)+(1957120140670039/20000000000000000000 : ℝ)=(50020453255601842543/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31120910500334891/100000000000000000000 : ℝ) ≤ ((35320320222649209181/35330000000000000000 : ℝ)+2*(506195133561/353300000000000 : ℝ)*(2943/20000 : ℝ))^(4315/1024 : ℝ) := by
    rw [show (35320320222649209181/35330000000000000000 : ℝ)+2*(506195133561/353300000000000 : ℝ)*(2943/20000 : ℝ)=(10001476803121967/10000000000000000 : ℝ) by norm_num, show 1+2*(31120910500334891/100000000000000000000 : ℝ)=(50031120910500334891/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35320320222649209181/35330000000000000000 : ℝ)*(X 1 0+X 2 0)+(506195133561/353300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4315/1024 : ℝ)) (lo := (5591/50000 : ℝ)) (hi := (2943/20000 : ℝ)) (c := (35320320222649209181/35330000000000000000 : ℝ)) (alpha := (506195133561/353300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35320320222649209181/35330000000000000000 : ℝ)*(X 0 1+X 2 1)+(506195133561/353300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4315/1024 : ℝ)) (lo := (5591/50000 : ℝ)) (hi := (2943/20000 : ℝ)) (c := (35320320222649209181/35330000000000000000 : ℝ)) (alpha := (506195133561/353300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35320320222649209181/35330000000000000000 : ℝ)*(X 0 2+X 1 2)+(506195133561/353300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4315/1024 : ℝ)) (lo := (5591/50000 : ℝ)) (hi := (2943/20000 : ℝ)) (c := (35320320222649209181/35330000000000000000 : ℝ)) (alpha := (506195133561/353300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-116611773/625000000 : ℝ)*X 0 0+(5389354013/10000000000 : ℝ)*X 0 1+(5389354689/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5285348697/10000000000 : ℝ)*X 1 0+(-40166979/200000000 : ℝ)*X 1 1+(5389353967/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1321337127/2500000000 : ℝ)*X 2 0+(1347338541/2500000000 : ℝ)*X 2 1+(-1004174469/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1117710169/2500000000 : ℝ)*X 0 0+(2126449827/5000000000 : ℝ)*X 0 1+(4252899923/10000000000 : ℝ)*X 0 2+(1117710169/2500000000 : ℝ)*X 1 0+(2126449827/5000000000 : ℝ)*X 1 1+(4252899923/10000000000 : ℝ)*X 1 2+(1117710169/2500000000 : ℝ)*X 2 0+(2126449827/5000000000 : ℝ)*X 2 1+(4252899923/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-550210689/2500000000 : ℝ)*X 0 0+(5265227589/10000000000 : ℝ)*X 0 1+(5265227117/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5372481007/10000000000 : ℝ)*X 1 0+(-2058254391/10000000000 : ℝ)*X 1 1+(131630693/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5372481491/10000000000 : ℝ)*X 2 0+(263261363/500000000 : ℝ)*X 2 1+(-1029127177/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4174162011/10000000000 : ℝ)*X 0 0+(2200592931/5000000000 : ℝ)*X 0 1+(1100296529/2500000000 : ℝ)*X 0 2+(4174162011/10000000000 : ℝ)*X 1 0+(2200592931/5000000000 : ℝ)*X 1 1+(1100296529/2500000000 : ℝ)*X 1 2+(4174162011/10000000000 : ℝ)*X 2 0+(2200592931/5000000000 : ℝ)*X 2 1+(1100296529/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2130445299/10000000000 : ℝ)*X 0 0+(2589854399/5000000000 : ℝ)*X 0 1+(5403368301/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2637753077/5000000000 : ℝ)*X 1 0+(-2002583423/10000000000 : ℝ)*X 1 1+(1080673569/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5275505739/10000000000 : ℝ)*X 2 0+(216134731/400000000 : ℝ)*X 2 1+(-1001291699/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2251888059/5000000000 : ℝ)*X 0 0+(169445773/400000000 : ℝ)*X 0 1+(4236145007/10000000000 : ℝ)*X 0 2+(2251888059/5000000000 : ℝ)*X 1 0+(169445773/400000000 : ℝ)*X 1 1+(4236145007/10000000000 : ℝ)*X 1 2+(2251888059/5000000000 : ℝ)*X 2 0+(169445773/400000000 : ℝ)*X 2 1+(4236145007/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-968247897/5000000000 : ℝ)*X 0 0+(547269869/1000000000 : ℝ)*X 0 1+(5254146843/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2690128763/5000000000 : ℝ)*X 1 0+(-1031303113/5000000000 : ℝ)*X 1 1+(1050829307/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2690128651/5000000000 : ℝ)*X 2 0+(41048023/78125000 : ℝ)*X 2 1+(-2062605981/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2592019/6250000 : ℝ)*X 0 0+(110360309/250000000 : ℝ)*X 0 1+(2207206111/5000000000 : ℝ)*X 0 2+(2592019/6250000 : ℝ)*X 1 0+(110360309/250000000 : ℝ)*X 1 1+(2207206111/5000000000 : ℝ)*X 1 2+(2592019/6250000 : ℝ)*X 2 0+(110360309/250000000 : ℝ)*X 2 1+(2207206111/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62861/100000 : ℝ) ≤ (-11103971091512371520545372083/17665000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22915783/50000000000000 : ℝ)*(lower2) + (156319427/100000000000000 : ℝ)*(lower3) + (5344381/50000000000000 : ℝ)*(lower5) + (1468128070137527/50000000000000 : ℝ)*(major0) + (1468128070137527/50000000000000 : ℝ)*(major1) + (1468128070137527/50000000000000 : ℝ)*(major2) + (131086373/50000000000000 : ℝ)*(sp2) + (292963599/50000000000000 : ℝ)*(sp3) + (1000628744461947/25000000000000 : ℝ)*(sp4) + (1000585376755871/25000000000000 : ℝ)*(sp5) + (2001264241714343/50000000000000 : ℝ)*(sp6) + (472733953639703/25000000000000 : ℝ)*(sp7) + (3441938411/25000000000000 : ℝ)*(sp8) + (187238577949/100000000000000 : ℝ)*(sp13) + (189093640048601/10000000000000 : ℝ)*(f.failure) + (500316093200179/12500000000000 : ℝ)*(f.sum) + (14803912259773/8832500000000000000000000000 : ℝ)*base66 + (959249012905735387/1766500000000000000000000000000000 : ℝ)*base67 + (9123010001443264613/1766500000000000000000000000000000 : ℝ)*base70 + (8588985314817264613/1766500000000000000000000000000000 : ℝ)*base72 + (2477410328989/1104062500000000000000000000 : ℝ)*base73 + (5714772870750764613/1766500000000000000000000000000000 : ℝ)*base76 + (22788333854735387/1766500000000000000000000000000000 : ℝ)*base77 + (266760415515735387/1766500000000000000000000000000000 : ℝ)*base79 + (20913755017779/4416250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (4616467/500000000000000000000 : ℝ)*base89 + (4616467/500000000000000000000 : ℝ)*base91 + (4616467/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (7371/12500 : ℝ) ≤ (5208606557320651749109894827/8832500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1373953/25000000000000 : ℝ)*(lower0) + (11940417/12500000000000 : ℝ)*(lower1) + (5933659/25000000000000 : ℝ)*(lower3) + (101732371/100000000000000 : ℝ)*(lower5) + (1502711244480639/50000000000000 : ℝ)*(major0) + (1502711244480639/50000000000000 : ℝ)*(major1) + (1502711244480639/50000000000000 : ℝ)*(major2) + (2027844938162831/50000000000000 : ℝ)*(sp0) + (101390772298179/2500000000000 : ℝ)*(sp1) + (811141754217/20000000000 : ℝ)*(sp2) + (1935470665755751/100000000000000 : ℝ)*(sp3) + (4283783051/50000000000000 : ℝ)*(sp7) + (38939578921/50000000000000 : ℝ)*(sp9) + (18894759339/100000000000000 : ℝ)*(sp12) + (483869808330463/25000000000000 : ℝ)*(f.failure) + (811141754217/20000000000 : ℝ)*(f.sum) + (31155774133341/8832500000000000000000000000 : ℝ)*base66 + (5114292827837553341/1766500000000000000000000000000000 : ℝ)*base68 + (17063402820886553341/1766500000000000000000000000000000 : ℝ)*base70 + (5398605503194446659/1766500000000000000000000000000000 : ℝ)*base71 + (40379827840239/8832500000000000000000000000 : ℝ)*base73 + (17630605329334053341/1766500000000000000000000000000000 : ℝ)*base76 + (20311557820296446659/1766500000000000000000000000000000 : ℝ)*base77 + (3819264249176446659/1766500000000000000000000000000000 : ℝ)*base79 + (223864297142367/17665000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/50000000000000 : ℝ)*base85 + (3446379/1250000000000000000000 : ℝ)*base90 + (3446379/1250000000000000000000 : ℝ)*base92 + (3446379/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (20009/25000 : ℝ) ≤ (282775666690353105424037727541911/353300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20485949/25000000000000 : ℝ)*(upper0) + (96244731/100000000000000 : ℝ)*(upper2) + (5393431/20000000000000 : ℝ)*(lower3) + (931659/12500000000000 : ℝ)*(lower4) + (663385596912223/20000000000000 : ℝ)*(major0) + (663385596912223/20000000000000 : ℝ)*(major1) + (663385596912223/20000000000000 : ℝ)*(major2) + (83159721571/100000000000000 : ℝ)*(sp2) + (45148197623/100000000000000 : ℝ)*(sp3) + (12806789427/100000000000000 : ℝ)*(sp4) + (447107625505593/10000000000000 : ℝ)*(sp8) + (1117772265461339/25000000000000 : ℝ)*(sp9) + (2235502951061893/50000000000000 : ℝ)*(sp10) + (106802114623033/5000000000000 : ℝ)*(sp11) + (534021860164571/25000000000000 : ℝ)*(f.failure) + (1117772265461339/25000000000000 : ℝ)*(f.sum) + (2352988667857/706600000000000000000000000 : ℝ)*base65 + (1217766715327980637/706600000000000000000000000000000 : ℝ)*base68 + (2458290600517780637/706600000000000000000000000000000 : ℝ)*base70 + (3459076469409819363/706600000000000000000000000000000 : ℝ)*base71 + (14826548546421/3533000000000000000000000000 : ℝ)*base73 + (6671256315637619363/706600000000000000000000000000000 : ℝ)*base75 + (535622770363019363/706600000000000000000000000000000 : ℝ)*base77 + (1617262883775419363/706600000000000000000000000000000 : ℝ)*base79 + (2151748053811/883250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (18880457/1250000000000000000000 : ℝ)*base89 + (18880457/1250000000000000000000 : ℝ)*base91 + (18880457/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-84407/100000 : ℝ) ≤ (-372749249843303709824183193264297/441625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (231468391/100000000000000 : ℝ)*(lower0) + (102727719/50000000000000 : ℝ)*(lower1) + (113863437/100000000000000 : ℝ)*(lower2) + (30380379/100000000000000 : ℝ)*(lower3) + (9636819/12500000000000 : ℝ)*(lower4) + (838388866303879/25000000000000 : ℝ)*(major0) + (838388866303879/25000000000000 : ℝ)*(major1) + (838388866303879/25000000000000 : ℝ)*(major2) + (142585210841/50000000000000 : ℝ)*(sp5) + (53050202993/50000000000000 : ℝ)*(sp6) + (4575570221901233/100000000000000 : ℝ)*(sp12) + (4575285051479551/100000000000000 : ℝ)*(sp13) + (4575464121495247/100000000000000 : ℝ)*(sp14) + (2159675381600321/100000000000000 : ℝ)*(sp15) + (2159675381600321/100000000000000 : ℝ)*(f.failure) + (4575570221901233/100000000000000 : ℝ)*(f.sum) + (144421670120903/8832500000000000000000000000 : ℝ)*base65 + (3336887184377886901/883250000000000000000000000000000 : ℝ)*base68 + (9019225324601363099/883250000000000000000000000000000 : ℝ)*base69 + (54667447313655386901/883250000000000000000000000000000 : ℝ)*base72 + (3883963460747/552031250000000000000000000 : ℝ)*base74 + (25941700538751863099/883250000000000000000000000000000 : ℝ)*base75 + (17077356697354613099/883250000000000000000000000000000 : ℝ)*base77 + (1837660535118613099/883250000000000000000000000000000 : ℝ)*base79 + (319734343415339/17665000000000000000000000000 : ℝ)*base82 + (9725707/5000000000000000000000 : ℝ)*base89 + (9725707/5000000000000000000000 : ℝ)*base91 + (9725707/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1356_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77640267/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2943/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5591/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62861/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(7371/12500 : ℝ) else (20009/25000 : ℝ) ≤ X j i ∧ X j i ≤ (84407/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1356_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1356_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77640267/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14723/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (447/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62861/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(7371/12500 : ℝ) else (20009/25000 : ℝ) ≤ X j i ∧ X j i ≤ (84407/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1356_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1356_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1356_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77640267/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14723/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (447/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62861/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(7371/12500 : ℝ) else (20009/25000 : ℝ) ≤ X j i ∧ X j i ≤ (84407/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1356_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

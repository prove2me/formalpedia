-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.box_nonnegative_w1260
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:53:39.080992+00:00
-- url     : https://prove2.me/submissions/7846565e-9c65-4365-9ac2-8f429a87e859

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_nonnegative_of_split_curvature_margins
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
namespace HlawkaSchatten.DiagonalCutoff12
theorem norm_cap_of_power_budget {p a U : ℝ} (hp : 0 < p) (ha : 0 ≤ a)
    (hap : a ≤ p) (hU : 0 ≤ U) (b x : Fin 3 → ℝ)
    (hb0 : ∀ i, 0 ≤ b i) (hb1 : ∀ i, b i ≤ 1)
    (hx : ∀ i, |x i| ≤ U*b i) (hbudget : (∑ i, (b i)^a) ≤ 1) :
    lpNorm p x ≤ U := by
  have hs : (∑ i, (b i)^p) ≤ 1 :=
    (Finset.sum_le_sum fun i _ => Real.rpow_le_rpow_of_exponent_ge'
      (hb0 i) (hb1 i) ha hap).trans hbudget
  have hsum : (∑ i, ‖x i‖^p) ≤ U^p := by
    calc
      _ ≤ ∑ i, U^p*(b i)^p := by
        apply Finset.sum_le_sum
        intro i _
        rw [Real.norm_eq_abs, ← Real.mul_rpow hU (hb0 i)]
        exact Real.rpow_le_rpow (abs_nonneg _) (hx i) hp.le
      _ = U^p*(∑ i, (b i)^p) := by rw [Finset.mul_sum]
      _ ≤ U^p*1 := mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hU p)
      _ = U^p := mul_one _
  have h := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg (x i)) p)
    hsum (one_div_nonneg.mpr hp.le)
  rw [one_div, Real.rpow_rpow_inv hU hp.ne'] at h
  simpa only [lpNorm, one_div] using h
end HlawkaSchatten.DiagonalCutoff12
namespace HlawkaSchatten.DiagonalCutoff6
theorem norm_cap_power_sum {p a C : ℝ} (hp : 0 < p) (ha : 0 ≤ a)
    (hap : a ≤ p) (hC : 0 < C) (x : Fin 3 → ℝ)
    (hx : ∀ i, |x i| ≤ C) (hbudget : (∑ i, |x i|^a) ≤ C^a) :
    lpNorm p x ≤ C := by
  apply HlawkaSchatten.DiagonalCutoff12.norm_cap_of_power_budget hp ha hap hC.le
    (fun i => |x i|/C) x
  · intro i; positivity
  · intro i; exact (div_le_one hC).mpr (hx i)
  · intro i; rw [mul_div_cancel₀ _ hC.ne']
  · simp_rw [Real.div_rpow (abs_nonneg _) hC.le]
    rw [← Finset.sum_div]
    exact (div_le_one (Real.rpow_pos_of_pos hC a)).mpr hbudget
end HlawkaSchatten.DiagonalCutoff6

namespace HlawkaSchatten.DiagonalConstruction
theorem cyclicA_pos {p t : ℝ} (ht : 0 ≤ t) : 0 < cyclicA p t := by
  unfold cyclicA
  exact Real.rpow_pos_of_pos (by positivity) _

/-- The cyclic pair-sum norm is nonneg. -/
theorem cyclicB_nonneg (p t : ℝ) : 0 ≤ cyclicB p t := by
  unfold cyclicB
  positivity

/-- Raising `cyclicA` to the `p`-th power recovers `t^p + 2`. -/
theorem cyclicA_rpow {p t : ℝ} (hp : 0 < p) (ht : 0 ≤ t) :
    cyclicA p t ^ p = t ^ p + 2 := by
  rw [cyclicA, ← Real.rpow_mul (by positivity : 0 ≤ t ^ p + 2),
    one_div_mul_cancel hp.ne', Real.rpow_one]

/-- Raising `cyclicB` to the `p`-th power recovers `2|1-t|^p + 2^p`. -/
theorem cyclicB_rpow {p : ℝ} (hp : 0 < p) (t : ℝ) :
    cyclicB p t ^ p = 2 * |1 - t| ^ p + (2 : ℝ) ^ p := by
  rw [cyclicB, ← Real.rpow_mul (by positivity :
    0 ≤ 2 * |1 - t| ^ p + (2 : ℝ) ^ p), one_div_mul_cancel hp.ne', Real.rpow_one]

/-- The denominator of the cyclic ratio is strictly positive for `p > 1`. -/
theorem cyclic_denominator_pos {p t : ℝ} (hp : 1 < p) (ht : 0 ≤ t) :
    0 < 6 * cyclicA p t - 3 * cyclicB p t := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have habs : |1 - t| ^ p ≤ 1 + t ^ p := by
    rcases le_total t 1 with h | h
    · have hpow := Real.rpow_le_rpow (abs_nonneg (1 - t))
        (show |1 - t| ≤ 1 by rw [abs_of_nonneg (sub_nonneg.mpr h)]; linarith) hp0.le
      rw [Real.one_rpow] at hpow
      linarith [Real.rpow_nonneg ht p]
    · have hpow := Real.rpow_le_rpow (abs_nonneg (1 - t))
        (show |1 - t| ≤ t by rw [abs_of_nonpos (sub_nonpos.mpr h)]; linarith) hp0.le
      linarith
  have htwo : (2 : ℝ) < (2 : ℝ) ^ p := by
    simpa using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hp
  have hlt : cyclicB p t ^ p < (2 * cyclicA p t) ^ p := by
    rw [cyclicB_rpow hp0, Real.mul_rpow (by norm_num) (cyclicA_pos ht).le,
      cyclicA_rpow hp0 ht]
    nlinarith [Real.rpow_nonneg ht p]
  have h := (Real.rpow_lt_rpow_iff (cyclicB_nonneg p t)
    (mul_nonneg (by norm_num) (cyclicA_pos ht).le) hp0).mp hlt
  linarith

/-- `cyclicA p` is continuous in `t`. -/
theorem continuous_cyclicA {p : ℝ} (hp : 0 < p) : Continuous (cyclicA p) := by
  exact ((Real.continuous_rpow_const hp.le).add continuous_const).rpow_const
    (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))

/-- `cyclicB p` is continuous in `t`. -/
theorem continuous_cyclicB {p : ℝ} (hp : 0 < p) : Continuous (cyclicB p) := by
  apply Continuous.rpow_const _ (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))
  exact (continuous_const.mul
    ((continuous_const.sub continuous_id).abs.rpow_const
      (fun _ ↦ Or.inr hp.le))).add continuous_const

/-- `cyclicRatio p` is continuous on `[0, ∞)`. -/
theorem continuousOn_cyclicRatio {p : ℝ} (hp : 1 < p) :
    ContinuousOn (cyclicRatio p) (Set.Ici 0) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  apply ContinuousOn.div
  · exact ((continuous_const.mul (continuous_cyclicA hp0)).sub
      (continuous_const.mul (continuous_const.sub continuous_id).abs)).continuousOn
  · exact ((continuous_const.mul (continuous_cyclicA hp0)).sub
      (continuous_const.mul (continuous_cyclicB hp0))).continuousOn
  · intro t ht
    exact (cyclic_denominator_pos hp ht).ne'

/-- The cyclic constant is attained at some `t ∈ [1/2, 2]`. -/
theorem cyclic_maximum_attained {p : ℝ} (hp : 1 < p) :
    ∃ t ∈ Set.Icc (1 / 2 : ℝ) 2, cyclicRatio p t = cyclicConstant p := by
  have hc := (continuousOn_cyclicRatio hp).mono
    (show Set.Icc (1 / 2 : ℝ) 2 ⊆ Set.Ici 0 from fun t ht ↦ by
      simp only [Set.mem_Ici]; linarith [ht.1])
  obtain ⟨t, ht, heq⟩ := isCompact_Icc.exists_sSup_image_eq
    (Set.nonempty_Icc.mpr (by norm_num : (1 / 2 : ℝ) ≤ 2)) hc
  exact ⟨t, ht, heq.symm⟩

/-- Every cyclic ratio on `[1/2, 2]` is at most `cyclicConstant p`. -/
theorem cyclicRatio_le_constant {p t : ℝ} (hp : 1 < p)
    (ht : t ∈ Set.Icc (1 / 2 : ℝ) 2) : cyclicRatio p t ≤ cyclicConstant p := by
  have hc := (continuousOn_cyclicRatio hp).mono
    (show Set.Icc (1 / 2 : ℝ) 2 ⊆ Set.Ici 0 from fun s hs ↦ by
      simp only [Set.mem_Ici]; linarith [hs.1])
  exact le_csSup (isCompact_Icc.image_of_continuousOn hc).bddAbove
    (Set.mem_image_of_mem (cyclicRatio p) ht)

/-- At `t = 2`, the cyclic ratio equals 1. -/
theorem cyclicRatio_two (p : ℝ) : cyclicRatio p 2 = 1 := by
  have hA : 0 < cyclicA p 2 := cyclicA_pos (by norm_num)
  have hB : cyclicB p 2 = cyclicA p 2 := by
    norm_num [cyclicA, cyclicB, add_comm]
  rw [cyclicRatio, hB]
  norm_num only [sub_self, abs_zero, mul_zero, sub_zero]
  have hden : 6 * cyclicA p 2 - 3 * cyclicA p 2 = 3 * cyclicA p 2 := by ring
  rw [hden, div_self (by positivity)]

/-- The cyclic constant is at least 1. -/
theorem one_le_cyclicConstant {p : ℝ} (hp : 1 < p) : 1 ≤ cyclicConstant p := by
  rw [← cyclicRatio_two p]
  exact cyclicRatio_le_constant hp (by norm_num)


end HlawkaSchatten.DiagonalConstruction

set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

namespace HlawkaSchatten.DiagonalCutoff4

theorem cyclicA_eq_norm {p t : ℝ} (ht : 0 ≤ t) :
    cyclicA p t = lpNorm p ![t,1,1] := by
  simp only [cyclicA,lpNorm,Fin.sum_univ_three]
  congr 1
  change t^p+2=‖t‖^p+‖(1:ℝ)‖^p+‖(1:ℝ)‖^p
  simp [Real.norm_eq_abs,abs_of_nonneg ht]
  ring

theorem cyclicB_eq_norm (p t : ℝ) :
    cyclicB p t = lpNorm p ![2,1-t,1-t] := by
  simp only [cyclicB,lpNorm,Fin.sum_univ_three]
  congr 1
  change 2*|1-t|^p+2^p=‖(2:ℝ)‖^p+‖1-t‖^p+‖1-t‖^p
  norm_num only [Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2)]
  ring

/-- A witness bound retaining the small positive tails in the pair norm. -/
theorem cyclicConstant_lower_from_bounds {p k t AU CU BL : ℝ}
    (hp : 1 < p) (ht : t ∈ Set.Icc (1/2 : ℝ) 2) (hk : 1/2 ≤ k)
    (hA : cyclicA p t ≤ AU) (hC : (3 : ℝ)^(1/p) ≤ CU) (hB : BL ≤ cyclicB p t)
    (hmargin : (6*k-3)*AU+CU*(2-t) < 3*k*BL) :
    k < cyclicConstant p := by
  have hden := cyclic_denominator_pos hp (show 0 ≤ t by linarith [ht.1])
  have h1 := mul_le_mul_of_nonneg_left hA (show 0 ≤ 6*k-3 by linarith)
  have h2 := mul_le_mul_of_nonneg_right hC (show 0 ≤ 2-t by linarith [ht.2])
  have h3 := mul_le_mul_of_nonneg_left hB (show 0 ≤ 3*k by linarith)
  have hratio : k < cyclicRatio p t := by
    rw [cyclicRatio,abs_of_nonneg (show 0 ≤ 2-t by linarith [ht.2]),lt_div_iff₀ hden]
    nlinarith only [h1,h2,h3,hmargin]
  exact hratio.trans_le (cyclicRatio_le_constant hp ht)

/-- An affine supporting line for the singleton norm and a uniform pair cap
give a one-dimensional interval bound for the cyclic quotient. -/
theorem cyclicRatio_upper_from_affine {p t K alpha beta CL BU : ℝ}
    (hp : 1 < p) (ht : t ∈ Set.Icc (1/2 : ℝ) 2) (hK : 1/2 ≤ K)
    (hA : alpha*t+beta ≤ cyclicA p t) (hC : CL ≤ (3 : ℝ)^(1/p))
    (hB : cyclicB p t ≤ BU)
    (hmargin : 3*K*BU ≤ (6*K-3)*(alpha*t+beta)+CL*(2-t)) :
    cyclicRatio p t ≤ K := by
  have hden := cyclic_denominator_pos hp (show 0 ≤ t by linarith [ht.1])
  have h1 := mul_le_mul_of_nonneg_left hA (show 0 ≤ 6*K-3 by linarith)
  have h2 := mul_le_mul_of_nonneg_right hC (show 0 ≤ 2-t by linarith [ht.2])
  have h3 := mul_le_mul_of_nonneg_left hB (show 0 ≤ 3*K by linarith)
  rw [cyclicRatio,abs_of_nonneg (show 0 ≤ 2-t by linarith [ht.2]),div_le_iff₀ hden]
  nlinarith only [h1,h2,h3,hmargin]

theorem cyclicConstant_upper_of_ratios {p K : ℝ} (hp : 1 < p)
    (h : ∀ t ∈ Set.Icc (1/2 : ℝ) 2, cyclicRatio p t ≤ K) :
    cyclicConstant p ≤ K := by
  obtain ⟨t,ht,he⟩ := cyclic_maximum_attained hp
  rw [← he]
  exact h t ht

theorem cyclicA_cap_from_power {p a t C : ℝ}
    (hp : 0 < p) (ha : 0 ≤ a) (hap : a ≤ p)
    (ht : 0 ≤ t) (htC : t ≤ C) (hC : 1 ≤ C)
    (hbudget : t^a+2 ≤ C^a) : cyclicA p t ≤ C := by
  rw [cyclicA_eq_norm ht]
  apply norm_cap_power_sum hp ha hap (by linarith)
  · intro i; fin_cases i <;> simp [abs_of_nonneg ht] <;> linarith
  · simp [Fin.sum_univ_three,abs_of_nonneg ht]
    nlinarith only [hbudget]

theorem cyclicB_cap_from_power {p a t H C : ℝ}
    (hp : 0 < p) (ha : 0 ≤ a) (hap : a ≤ p)
    (hH : 0 ≤ H) (hHC : H ≤ C) (hC : 2 ≤ C) (ht : |1-t| ≤ H)
    (hbudget : (2 : ℝ)^a+2*H^a ≤ C^a) : cyclicB p t ≤ C := by
  rw [cyclicB_eq_norm]
  apply norm_cap_power_sum hp ha hap (by linarith)
  · intro i; fin_cases i <;> simp <;> linarith
  · have htail := Real.rpow_le_rpow (abs_nonneg (1-t)) ht ha
    simp [Fin.sum_univ_three]
    nlinarith only [htail,hbudget]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle
namespace HlawkaSchatten.DiagonalCutoff4
theorem lower_support_w1260 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1999373043/2000000000 : ℝ)*x 0 + (8077289/5000000000 : ℝ)*x 1 + (8077289/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1999373043/2000000000 : ℝ)^8453 ≤ (6247414421401/6250000000000 : ℝ)^6405 := by
    have hnat : (1999373043 : ℕ)^8453*6250000000000^6405 ≤ 6247414421401^6405*2000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1999373043 2000000000 6247414421401 6250000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8077289/5000000000 : ℝ)^8453 ≤ (10342311183/50000000000000 : ℝ)^6405 := by
    have hnat : (8077289 : ℕ)^8453*50000000000000^6405 ≤ 10342311183^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8077289 5000000000 10342311183 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8077289/5000000000 : ℝ)^8453 ≤ (10342311183/50000000000000 : ℝ)^6405 := by
    have hnat : (8077289 : ℕ)^8453*50000000000000^6405 ≤ 10342311183^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8077289 5000000000 10342311183 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1999373043/2000000000 : ℝ), (8077289/5000000000 : ℝ), (8077289/5000000000 : ℝ)] ![(6247414421401/6250000000000 : ℝ), (10342311183/50000000000000 : ℝ), (10342311183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1999373043/2000000000 : ℝ)|^8453 ≤ (6247414421401/6250000000000 : ℝ)^6405
        have hw : |(1999373043/2000000000 : ℝ)|=(1999373043/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8077289/5000000000 : ℝ)|^8453 ≤ (10342311183/50000000000000 : ℝ)^6405
        have hw : |(8077289/5000000000 : ℝ)|=(8077289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8077289/5000000000 : ℝ)|^8453 ≤ (10342311183/50000000000000 : ℝ)^6405
        have hw : |(8077289/5000000000 : ℝ)|=(8077289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem scalar_lower_w1260 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) :
    (151781167/100000000 : ℝ) < cyclicConstant p := by
  have htpow : (743890599/1000000000 : ℝ) ^ (2113/512 : ℝ) ≤ (117973359653611/400000000000000 : ℝ) := by
    have hpowers : (743890599/1000000000 : ℝ)^2113 ≤ (117973359653611/400000000000000 : ℝ)^512 := by
      have hnat : (743890599 : ℕ)^2113*400000000000000^512 ≤ 117973359653611^512*1000000000^2113 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        743890599 1000000000 117973359653611 400000000000000 2113 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (743890599/1000000000 : ℝ)) (X := (117973359653611/400000000000000 : ℝ)) (by norm_num) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hAU : (917973359653611/400000000000000 : ℝ) ≤ (3057440629240759/2500000000000000 : ℝ) ^ (2113/512 : ℝ) := by
    have hpowers : (917973359653611/400000000000000 : ℝ)^512 ≤ (3057440629240759/2500000000000000 : ℝ)^2113 := by
      have hnat : (917973359653611 : ℕ)^512*2500000000000000^2113 ≤ 3057440629240759^2113*400000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        917973359653611 400000000000000 3057440629240759 2500000000000000 512 2113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3057440629240759/2500000000000000 : ℝ)) (X := (917973359653611/400000000000000 : ℝ)) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hCU : (3 : ℝ) ^ (512/2113 : ℝ) ≤ (13050015234115827/10000000000000000 : ℝ) := by
    have hpowers : (3 : ℝ)^512 ≤ (13050015234115827/10000000000000000 : ℝ)^2113 := by
      have hnat : (3 : ℕ)^512*10000000000000000^2113 ≤ 13050015234115827^2113*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13050015234115827 10000000000000000 512 2113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3 : ℝ)) (X := (13050015234115827/10000000000000000 : ℝ)) (by norm_num) (by norm_num) 512 2113 (by norm_num) hpowers
    exact h
  have hA : cyclicA p (743890599/1000000000 : ℝ) ≤ (3057440629240759/2500000000000000 : ℝ) := by
    apply cyclicA_cap_from_power (a := (2113/512 : ℝ)) (by linarith only [hpa]) (by norm_num) hpa
      (by norm_num) (by norm_num) (by norm_num)
    have h : (743890599/1000000000 : ℝ)^(2113/512 : ℝ)+2 ≤ (117973359653611/400000000000000 : ℝ)+2 := add_le_add htpow (le_refl (2:ℝ))
    rw [show (117973359653611/400000000000000 : ℝ)+2=(917973359653611/400000000000000 : ℝ) by norm_num] at h
    exact h.trans hAU
  have hC : (3 : ℝ)^(1/p) ≤ (13050015234115827/10000000000000000 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < (2113/512 : ℝ)) hpa)
    rw [show (1:ℝ)/(2113/512 : ℝ)=(512/2113 : ℝ) by norm_num] at h
    exact h.trans hCU
  have hB : (5000501277147493889/2500000000000000000 : ℝ) ≤ cyclicB p (743890599/1000000000 : ℝ) := by
    have h := lower_support_w1260 p hpa hpb ![2,1-(743890599/1000000000 : ℝ),1-(743890599/1000000000 : ℝ)]
    change (1999373043/2000000000 : ℝ)*2+(8077289/5000000000 : ℝ)*(1-(743890599/1000000000 : ℝ))+(8077289/5000000000 : ℝ)*(1-(743890599/1000000000 : ℝ)) ≤ lpNorm p ![2,1-(743890599/1000000000 : ℝ),1-(743890599/1000000000 : ℝ)] at h
    rw [cyclicB_eq_norm]
    norm_num at h ⊢
    linarith only [h]
  exact cyclicConstant_lower_from_bounds (by linarith only [hpa]) (by norm_num) (by norm_num)
    hA hC hB (by norm_num)
theorem upper_support_w1260_0 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (517841439/2500000000 : ℝ)*x 0 + (5344218591/10000000000 : ℝ)*x 1 + (5344218591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (517841439/2500000000 : ℝ)^8453 ≤ (78254583693/625000000000 : ℝ)^6405 := by
    have hnat : (517841439 : ℕ)^8453*625000000000^6405 ≤ 78254583693^6405*2500000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517841439 2500000000 78254583693 625000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5344218591/10000000000 : ℝ)^8453 ≤ (21869816646087/50000000000000 : ℝ)^6405 := by
    have hnat : (5344218591 : ℕ)^8453*50000000000000^6405 ≤ 21869816646087^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344218591 10000000000 21869816646087 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5344218591/10000000000 : ℝ)^8453 ≤ (21869816646087/50000000000000 : ℝ)^6405 := by
    have hnat : (5344218591 : ℕ)^8453*50000000000000^6405 ≤ 21869816646087^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344218591 10000000000 21869816646087 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(517841439/2500000000 : ℝ), (5344218591/10000000000 : ℝ), (5344218591/10000000000 : ℝ)] ![(78254583693/625000000000 : ℝ), (21869816646087/50000000000000 : ℝ), (21869816646087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(517841439/2500000000 : ℝ)|^8453 ≤ (78254583693/625000000000 : ℝ)^6405
        have hw : |(517841439/2500000000 : ℝ)|=(517841439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5344218591/10000000000 : ℝ)|^8453 ≤ (21869816646087/50000000000000 : ℝ)^6405
        have hw : |(5344218591/10000000000 : ℝ)|=(5344218591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5344218591/10000000000 : ℝ)|^8453 ≤ (21869816646087/50000000000000 : ℝ)^6405
        have hw : |(5344218591/10000000000 : ℝ)|=(5344218591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem ratio_upper_w1260_0 (p t : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ))
    (htlo : (1/2 : ℝ) ≤ t) (hthi : t ≤ (1 : ℝ)) : cyclicRatio p t ≤ (31/20 : ℝ) := by
  have hCL : (130496042659/100000000000 : ℝ) ≤ (3 : ℝ) ^ (2048/8453 : ℝ) := by
    have hpowers : (130496042659/100000000000 : ℝ)^8453 ≤ (3 : ℝ)^2048 := by
      have hnat : (130496042659 : ℕ)^8453*1^2048 ≤ 3^2048*100000000000^8453 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        130496042659 100000000000 3 1 8453 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3 : ℝ)) (X := (130496042659/100000000000 : ℝ)) (by norm_num) 2048 8453 (by norm_num) hpowers
    exact h
  have hHpow : (1/2 : ℝ) ^ (2113/512 : ℝ) ≤ (8943002346247/156250000000000 : ℝ) := by
    have hpowers : (1/2 : ℝ)^2113 ≤ (8943002346247/156250000000000 : ℝ)^512 := by
      have hnat : (1 : ℕ)^2113*156250000000000^512 ≤ 8943002346247^512*2^2113 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 2 8943002346247 156250000000000 2113 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (8943002346247/156250000000000 : ℝ)) (by norm_num) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hTwopow : (2 : ℝ) ^ (2113/512 : ℝ) ≤ (174717610429311537/10000000000000000 : ℝ) := by
    have hpowers : (2 : ℝ)^2113 ≤ (174717610429311537/10000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2113*10000000000000000^512 ≤ 174717610429311537^512*1^2113 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 174717610429311537 10000000000000000 2113 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2 : ℝ)) (X := (174717610429311537/10000000000000000 : ℝ)) (by norm_num) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hBU : (175862314729631153/10000000000000000 : ℝ) ≤ (20031672469148521/10000000000000000 : ℝ) ^ (2113/512 : ℝ) := by
    have hpowers : (175862314729631153/10000000000000000 : ℝ)^512 ≤ (20031672469148521/10000000000000000 : ℝ)^2113 := by
      have hnat : (175862314729631153 : ℕ)^512*10000000000000000^2113 ≤ 20031672469148521^2113*10000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        175862314729631153 10000000000000000 20031672469148521 10000000000000000 512 2113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (20031672469148521/10000000000000000 : ℝ)) (X := (175862314729631153/10000000000000000 : ℝ)) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hA : (517841439/2500000000 : ℝ)*t+(5344218591/5000000000 : ℝ) ≤ cyclicA p t := by
    have h := upper_support_w1260_0 p hpa hpb ![t,1,1]
    change (517841439/2500000000 : ℝ)*t+(5344218591/10000000000 : ℝ)*1+(5344218591/10000000000 : ℝ)*1 ≤ lpNorm p ![t,1,1] at h
    rw [cyclicA_eq_norm (by linarith only [htlo] : 0 ≤ t)]
    norm_num at h ⊢
    linarith only [h]
  have hC : (130496042659/100000000000 : ℝ) ≤ (3 : ℝ)^(1/p) := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
      (one_div_le_one_div_of_le (by linarith only [hpa] : (0 : ℝ) < p) hpb)
    rw [show (1:ℝ)/(8453/2048 : ℝ)=(2048/8453 : ℝ) by norm_num] at h
    exact hCL.trans h
  have hB : cyclicB p t ≤ (20031672469148521/10000000000000000 : ℝ) := by
    apply cyclicB_cap_from_power (a := (2113/512 : ℝ)) (H := (1/2 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num)
    · exact abs_le.mpr ⟨by linarith only [htlo,hthi],by linarith only [htlo,hthi]⟩
    · have hb : (174717610429311537/10000000000000000 : ℝ)+2*(8943002346247/156250000000000 : ℝ) ≤ (20031672469148521/10000000000000000 : ℝ)^(2113/512 : ℝ) := by
        rw [show (174717610429311537/10000000000000000 : ℝ)+2*(8943002346247/156250000000000 : ℝ)=(175862314729631153/10000000000000000 : ℝ) by norm_num]
        exact hBU
      have hh := sum_two_bounds hTwopow hHpow hb
      simpa only [add_comm] using hh
  apply cyclicRatio_upper_from_affine (by linarith only [hpa]) ⟨by linarith only [htlo,hthi],by linarith only [htlo,hthi]⟩ (by norm_num) hA hC hB
  norm_num
  linarith only [htlo,hthi]
theorem upper_support_w1260_1 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (543733511/1250000000 : ℝ)*x 0 + (543733511/1250000000 : ℝ)*x 1 + (543733511/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543733511/1250000000 : ℝ)^8453 ≤ (16666666663453/50000000000000 : ℝ)^6405 := by
    have hnat : (543733511 : ℕ)^8453*50000000000000^6405 ≤ 16666666663453^6405*1250000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543733511 1250000000 16666666663453 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543733511/1250000000 : ℝ)^8453 ≤ (16666666663453/50000000000000 : ℝ)^6405 := by
    have hnat : (543733511 : ℕ)^8453*50000000000000^6405 ≤ 16666666663453^6405*1250000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543733511 1250000000 16666666663453 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543733511/1250000000 : ℝ)^8453 ≤ (16666666663453/50000000000000 : ℝ)^6405 := by
    have hnat : (543733511 : ℕ)^8453*50000000000000^6405 ≤ 16666666663453^6405*1250000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543733511 1250000000 16666666663453 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543733511/1250000000 : ℝ), (543733511/1250000000 : ℝ), (543733511/1250000000 : ℝ)] ![(16666666663453/50000000000000 : ℝ), (16666666663453/50000000000000 : ℝ), (16666666663453/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543733511/1250000000 : ℝ)|^8453 ≤ (16666666663453/50000000000000 : ℝ)^6405
        have hw : |(543733511/1250000000 : ℝ)|=(543733511/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(543733511/1250000000 : ℝ)|^8453 ≤ (16666666663453/50000000000000 : ℝ)^6405
        have hw : |(543733511/1250000000 : ℝ)|=(543733511/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(543733511/1250000000 : ℝ)|^8453 ≤ (16666666663453/50000000000000 : ℝ)^6405
        have hw : |(543733511/1250000000 : ℝ)|=(543733511/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem ratio_upper_w1260_1 (p t : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ))
    (htlo : (1 : ℝ) ≤ t) (hthi : t ≤ (3/2 : ℝ)) : cyclicRatio p t ≤ (31/20 : ℝ) := by
  have hCL : (130496042659/100000000000 : ℝ) ≤ (3 : ℝ) ^ (2048/8453 : ℝ) := by
    have hpowers : (130496042659/100000000000 : ℝ)^8453 ≤ (3 : ℝ)^2048 := by
      have hnat : (130496042659 : ℕ)^8453*1^2048 ≤ 3^2048*100000000000^8453 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        130496042659 100000000000 3 1 8453 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3 : ℝ)) (X := (130496042659/100000000000 : ℝ)) (by norm_num) 2048 8453 (by norm_num) hpowers
    exact h
  have hHpow : (1/2 : ℝ) ^ (2113/512 : ℝ) ≤ (8943002346247/156250000000000 : ℝ) := by
    have hpowers : (1/2 : ℝ)^2113 ≤ (8943002346247/156250000000000 : ℝ)^512 := by
      have hnat : (1 : ℕ)^2113*156250000000000^512 ≤ 8943002346247^512*2^2113 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 2 8943002346247 156250000000000 2113 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1/2 : ℝ)) (X := (8943002346247/156250000000000 : ℝ)) (by norm_num) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hTwopow : (2 : ℝ) ^ (2113/512 : ℝ) ≤ (174717610429311537/10000000000000000 : ℝ) := by
    have hpowers : (2 : ℝ)^2113 ≤ (174717610429311537/10000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2113*10000000000000000^512 ≤ 174717610429311537^512*1^2113 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 174717610429311537 10000000000000000 2113 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2 : ℝ)) (X := (174717610429311537/10000000000000000 : ℝ)) (by norm_num) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hBU : (175862314729631153/10000000000000000 : ℝ) ≤ (20031672469148521/10000000000000000 : ℝ) ^ (2113/512 : ℝ) := by
    have hpowers : (175862314729631153/10000000000000000 : ℝ)^512 ≤ (20031672469148521/10000000000000000 : ℝ)^2113 := by
      have hnat : (175862314729631153 : ℕ)^512*10000000000000000^2113 ≤ 20031672469148521^2113*10000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        175862314729631153 10000000000000000 20031672469148521 10000000000000000 512 2113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (20031672469148521/10000000000000000 : ℝ)) (X := (175862314729631153/10000000000000000 : ℝ)) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hA : (543733511/1250000000 : ℝ)*t+(543733511/625000000 : ℝ) ≤ cyclicA p t := by
    have h := upper_support_w1260_1 p hpa hpb ![t,1,1]
    change (543733511/1250000000 : ℝ)*t+(543733511/1250000000 : ℝ)*1+(543733511/1250000000 : ℝ)*1 ≤ lpNorm p ![t,1,1] at h
    rw [cyclicA_eq_norm (by linarith only [htlo] : 0 ≤ t)]
    norm_num at h ⊢
    linarith only [h]
  have hC : (130496042659/100000000000 : ℝ) ≤ (3 : ℝ)^(1/p) := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
      (one_div_le_one_div_of_le (by linarith only [hpa] : (0 : ℝ) < p) hpb)
    rw [show (1:ℝ)/(8453/2048 : ℝ)=(2048/8453 : ℝ) by norm_num] at h
    exact hCL.trans h
  have hB : cyclicB p t ≤ (20031672469148521/10000000000000000 : ℝ) := by
    apply cyclicB_cap_from_power (a := (2113/512 : ℝ)) (H := (1/2 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num)
    · exact abs_le.mpr ⟨by linarith only [htlo,hthi],by linarith only [htlo,hthi]⟩
    · have hb : (174717610429311537/10000000000000000 : ℝ)+2*(8943002346247/156250000000000 : ℝ) ≤ (20031672469148521/10000000000000000 : ℝ)^(2113/512 : ℝ) := by
        rw [show (174717610429311537/10000000000000000 : ℝ)+2*(8943002346247/156250000000000 : ℝ)=(175862314729631153/10000000000000000 : ℝ) by norm_num]
        exact hBU
      have hh := sum_two_bounds hTwopow hHpow hb
      simpa only [add_comm] using hh
  apply cyclicRatio_upper_from_affine (by linarith only [hpa]) ⟨by linarith only [htlo,hthi],by linarith only [htlo,hthi]⟩ (by norm_num) hA hC hB
  norm_num
  linarith only [htlo,hthi]
theorem upper_support_w1260_2 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (981918967/1250000000 : ℝ)*x 0 + (1105148263/5000000000 : ℝ)*x 1 + (1105148263/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (981918967/1250000000 : ℝ)^8453 ≤ (36359242951483/50000000000000 : ℝ)^6405 := by
    have hnat : (981918967 : ℕ)^8453*50000000000000^6405 ≤ 36359242951483^6405*1250000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      981918967 1250000000 36359242951483 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1105148263/5000000000 : ℝ)^8453 ≤ (6820378520559/50000000000000 : ℝ)^6405 := by
    have hnat : (1105148263 : ℕ)^8453*50000000000000^6405 ≤ 6820378520559^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105148263 5000000000 6820378520559 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1105148263/5000000000 : ℝ)^8453 ≤ (6820378520559/50000000000000 : ℝ)^6405 := by
    have hnat : (1105148263 : ℕ)^8453*50000000000000^6405 ≤ 6820378520559^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105148263 5000000000 6820378520559 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(981918967/1250000000 : ℝ), (1105148263/5000000000 : ℝ), (1105148263/5000000000 : ℝ)] ![(36359242951483/50000000000000 : ℝ), (6820378520559/50000000000000 : ℝ), (6820378520559/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(981918967/1250000000 : ℝ)|^8453 ≤ (36359242951483/50000000000000 : ℝ)^6405
        have hw : |(981918967/1250000000 : ℝ)|=(981918967/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1105148263/5000000000 : ℝ)|^8453 ≤ (6820378520559/50000000000000 : ℝ)^6405
        have hw : |(1105148263/5000000000 : ℝ)|=(1105148263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1105148263/5000000000 : ℝ)|^8453 ≤ (6820378520559/50000000000000 : ℝ)^6405
        have hw : |(1105148263/5000000000 : ℝ)|=(1105148263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem ratio_upper_w1260_2 (p t : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ))
    (htlo : (3/2 : ℝ) ≤ t) (hthi : t ≤ (2 : ℝ)) : cyclicRatio p t ≤ (31/20 : ℝ) := by
  have hCL : (130496042659/100000000000 : ℝ) ≤ (3 : ℝ) ^ (2048/8453 : ℝ) := by
    have hpowers : (130496042659/100000000000 : ℝ)^8453 ≤ (3 : ℝ)^2048 := by
      have hnat : (130496042659 : ℕ)^8453*1^2048 ≤ 3^2048*100000000000^8453 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        130496042659 100000000000 3 1 8453 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3 : ℝ)) (X := (130496042659/100000000000 : ℝ)) (by norm_num) 2048 8453 (by norm_num) hpowers
    exact h
  have hHpow : (1 : ℝ) ^ (2113/512 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^2113 ≤ (1 : ℝ)^512 := by
      have hnat : (1 : ℕ)^2113*1^512 ≤ 1^512*1^2113 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2113 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hTwopow : (2 : ℝ) ^ (2113/512 : ℝ) ≤ (174717610429311537/10000000000000000 : ℝ) := by
    have hpowers : (2 : ℝ)^2113 ≤ (174717610429311537/10000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2113*10000000000000000^512 ≤ 174717610429311537^512*1^2113 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 174717610429311537 10000000000000000 2113 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2 : ℝ)) (X := (174717610429311537/10000000000000000 : ℝ)) (by norm_num) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hBU : (194717610429311537/10000000000000000 : ℝ) ≤ (20532184260140607/10000000000000000 : ℝ) ^ (2113/512 : ℝ) := by
    have hpowers : (194717610429311537/10000000000000000 : ℝ)^512 ≤ (20532184260140607/10000000000000000 : ℝ)^2113 := by
      have hnat : (194717610429311537 : ℕ)^512*10000000000000000^2113 ≤ 20532184260140607^2113*10000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        194717610429311537 10000000000000000 20532184260140607 10000000000000000 512 2113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (20532184260140607/10000000000000000 : ℝ)) (X := (194717610429311537/10000000000000000 : ℝ)) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hA : (981918967/1250000000 : ℝ)*t+(1105148263/2500000000 : ℝ) ≤ cyclicA p t := by
    have h := upper_support_w1260_2 p hpa hpb ![t,1,1]
    change (981918967/1250000000 : ℝ)*t+(1105148263/5000000000 : ℝ)*1+(1105148263/5000000000 : ℝ)*1 ≤ lpNorm p ![t,1,1] at h
    rw [cyclicA_eq_norm (by linarith only [htlo] : 0 ≤ t)]
    norm_num at h ⊢
    linarith only [h]
  have hC : (130496042659/100000000000 : ℝ) ≤ (3 : ℝ)^(1/p) := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
      (one_div_le_one_div_of_le (by linarith only [hpa] : (0 : ℝ) < p) hpb)
    rw [show (1:ℝ)/(8453/2048 : ℝ)=(2048/8453 : ℝ) by norm_num] at h
    exact hCL.trans h
  have hB : cyclicB p t ≤ (20532184260140607/10000000000000000 : ℝ) := by
    apply cyclicB_cap_from_power (a := (2113/512 : ℝ)) (H := (1 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num)
    · exact abs_le.mpr ⟨by linarith only [htlo,hthi],by linarith only [htlo,hthi]⟩
    · have hb : (174717610429311537/10000000000000000 : ℝ)+2*(1 : ℝ) ≤ (20532184260140607/10000000000000000 : ℝ)^(2113/512 : ℝ) := by
        rw [show (174717610429311537/10000000000000000 : ℝ)+2*(1 : ℝ)=(194717610429311537/10000000000000000 : ℝ) by norm_num]
        exact hBU
      have hh := sum_two_bounds hTwopow hHpow hb
      simpa only [add_comm] using hh
  apply cyclicRatio_upper_from_affine (by linarith only [hpa]) ⟨by linarith only [htlo,hthi],by linarith only [htlo,hthi]⟩ (by norm_num) hA hC hB
  norm_num
  linarith only [htlo,hthi]
theorem scalar_upper_w1260 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) : cyclicConstant p ≤ (31/20 : ℝ) := by
  apply cyclicConstant_upper_of_ratios (by linarith)
  intro t ht
  by_cases ht1 : t ≤ 1
  · exact ratio_upper_w1260_0 p t hpa hpb ht.1 ht1
  by_cases ht2 : t ≤ 3/2
  · exact ratio_upper_w1260_1 p t hpa hpb (by linarith) ht2
  exact ratio_upper_w1260_2 p t hpa hpb (by linarith) ht.2
end HlawkaSchatten.DiagonalCutoff4

set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction
open scoped BigOperators
namespace HlawkaSchatten.DiagonalCutoff6

theorem rows_norm_cap_real {p a ell u v w U : ℝ}
    (hp : 0 < p) (ha : 0 ≤ a) (hap : a ≤ p)
    (hell : 0 ≤ ell) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hU : 0 < U) (huU : u ≤ U) (hwU : w ≤ U)
    (hbudget : (u/U)^a+2*(w/U)^a ≤ 1)
    (X : Fin 3 → Fin 3 → ℝ)
    (hbox : ∀ j i, if j=i then -u ≤ X j i ∧ X j i ≤ -ell
      else v ≤ X j i ∧ X j i ≤ w) : ∀ j, lpNorm p (X j) ≤ U := by
  intro j
  apply HlawkaSchatten.DiagonalCutoff12.norm_cap_of_power_budget hp ha hap hU.le
    (fun i => if j=i then u/U else w/U) (X j)
  · intro i;split_ifs <;> positivity
  · intro i;split_ifs
    · exact (div_le_one hU).mpr huU
    · exact (div_le_one hU).mpr hwU
  · intro i
    have hb := hbox j i
    by_cases hji : j=i
    · simp only [if_pos hji] at hb ⊢
      rw [mul_div_cancel₀ _ hU.ne']
      exact abs_le.mpr ⟨hb.1,by linarith [hb.2]⟩
    · simp only [if_neg hji] at hb ⊢
      rw [mul_div_cancel₀ _ hU.ne']
      exact abs_le.mpr ⟨by linarith [hb.1],hb.2⟩
  · fin_cases j <;> norm_num [Fin.sum_univ_three,Fin.ext_iff] <;> nlinarith only [hbudget]

end HlawkaSchatten.DiagonalCutoff6
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4

theorem box_nonnegative_w1260 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hbox : ∀ j i, if j=i then -(249/400 : ℝ) ≤ X j i ∧ X j i ≤ -(1856/3125 : ℝ)
      else (40081/50000 : ℝ) ≤ X j i ∧ X j i ≤ (16677/20000 : ℝ)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by
  have hKlo := scalar_lower_w1260 p hpa hpb
  have hKhi := scalar_upper_w1260 p hpa hpb
  have hKone := one_le_cyclicConstant (by linarith : (1 : ℝ) < p)
  have hdiagpow : (207500/340083 : ℝ) ^ (2113/512 : ℝ) ≤ (13016456862104096099/100000000000000000000 : ℝ) := by
    have hpowers : (207500/340083 : ℝ)^2113 ≤ (13016456862104096099/100000000000000000000 : ℝ)^512 := by
      have hnat : (207500 : ℕ)^2113*100000000000000000000^512 ≤ 13016456862104096099^512*340083^2113 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        207500 340083 13016456862104096099 100000000000000000000 2113 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (207500/340083 : ℝ)) (X := (13016456862104096099/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hoffpow : (92650/113361 : ℝ) ^ (2113/512 : ℝ) ≤ (8698284473939857849/20000000000000000000 : ℝ) := by
    have hpowers : (92650/113361 : ℝ)^2113 ≤ (8698284473939857849/20000000000000000000 : ℝ)^512 := by
      have hnat : (92650 : ℕ)^2113*20000000000000000000^512 ≤ 8698284473939857849^512*113361^2113 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        92650 113361 8698284473939857849 20000000000000000000 2113 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (92650/113361 : ℝ)) (X := (8698284473939857849/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have htotalpow : (536890/700643 : ℝ) ^ (2113/512 : ℝ) ≤ (33333189593030771407/100000000000000000000 : ℝ) := by
    have hpowers : (536890/700643 : ℝ)^2113 ≤ (33333189593030771407/100000000000000000000 : ℝ)^512 := by
      have hnat : (536890 : ℕ)^2113*100000000000000000000^512 ≤ 33333189593030771407^512*700643^2113 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        536890 700643 33333189593030771407 100000000000000000000 2113 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (536890/700643 : ℝ)) (X := (33333189593030771407/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have htailT : (16810527499/78618079880 : ℝ) ^ (1089/512 : ℝ) ≤ (3758951328135787089/100000000000000000000 : ℝ) := by
    have hpowers : (16810527499/78618079880 : ℝ)^1089 ≤ (3758951328135787089/100000000000000000000 : ℝ)^512 := by
      have hnat : (16810527499 : ℕ)^1089*100000000000000000000^512 ≤ 3758951328135787089^512*78618079880^1089 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16810527499 78618079880 3758951328135787089 100000000000000000000 1089 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16810527499/78618079880 : ℝ)) (X := (3758951328135787089/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1089 512 (by norm_num) hpowers
    exact h
  have htailC : (844097733/3283435520 : ℝ) ^ (1089/512 : ℝ) ≤ (2781021202655209377/50000000000000000000 : ℝ) := by
    have hpowers : (844097733/3283435520 : ℝ)^1089 ≤ (2781021202655209377/50000000000000000000 : ℝ)^512 := by
      have hnat : (844097733 : ℕ)^1089*50000000000000000000^512 ≤ 2781021202655209377^512*3283435520^1089 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        844097733 3283435520 2781021202655209377 50000000000000000000 1089 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (844097733/3283435520 : ℝ)) (X := (2781021202655209377/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1089 512 (by norm_num) hpowers
    exact h
  have hrows := rows_norm_cap_real (a := (2113/512 : ℝ)) (U := (1020249/1000000 : ℝ))
    (by linarith only [hpa] : (0 : ℝ) < p) (by norm_num) hpa
    (by norm_num : (0 : ℝ) ≤ (1856/3125 : ℝ)) (by norm_num : (0 : ℝ) ≤ (249/400 : ℝ))
    (by norm_num : (0 : ℝ) ≤ (40081/50000 : ℝ)) (by norm_num : (0 : ℝ) ≤ (16677/20000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (by
      rw [show (249/400 : ℝ)/(1020249/1000000 : ℝ)=(207500/340083 : ℝ) by norm_num, show (16677/20000 : ℝ)/(1020249/1000000 : ℝ)=(92650/113361 : ℝ) by norm_num]
      exact sum_two_bounds hdiagpow hoffpow (by norm_num)) X hbox
  have hcoord (i : Fin 3) : |(X 0+X 1+X 2) i| ≤ (53689/50000 : ℝ) := by
    have h00 := hbox 0 0; have h01 := hbox 0 1; have h02 := hbox 0 2
    have h10 := hbox 1 0; have h11 := hbox 1 1; have h12 := hbox 1 2
    have h20 := hbox 2 0; have h21 := hbox 2 1; have h22 := hbox 2 2
    norm_num [Fin.ext_iff] at h00 h01 h02 h10 h11 h12 h20 h21 h22
    fin_cases i
    · change |X 0 0+X 1 0+X 2 0| ≤ (53689/50000 : ℝ)
      apply abs_le.mpr
      constructor <;> linarith only [h00,h10,h20]
    · change |X 0 1+X 1 1+X 2 1| ≤ (53689/50000 : ℝ)
      apply abs_le.mpr
      constructor <;> linarith only [h01,h11,h21]
    · change |X 0 2+X 1 2+X 2 2| ≤ (53689/50000 : ℝ)
      apply abs_le.mpr
      constructor <;> linarith only [h02,h12,h22]
  have htotal : lpNorm p (X 0+X 1+X 2) ≤ (700643/500000 : ℝ) := by
    apply HlawkaSchatten.DiagonalCutoff12.norm_cap_of_power_budget (by linarith only [hpa] : (0 : ℝ) < p)
      (a := (2113/512 : ℝ)) (by norm_num) hpa (by norm_num : (0 : ℝ) ≤ (700643/500000 : ℝ))
      (fun _ : Fin 3 => (536890/700643 : ℝ)) (X 0+X 1+X 2)
    · intro i; norm_num
    · intro i; norm_num
    · intro i; norm_num; exact hcoord i
    · simpa only [Fin.sum_univ_three] using three_bounds htotalpow (by norm_num)
  have hpairs : ∀ i j l : Fin 3, i ≠ j → i ≠ l → j ≠ l → (40081/25000 : ℝ) ≤ X j i+X l i := by
    intro i j l hij hil hjl
    have hj := hbox j i; have hl := hbox l i
    simp only [if_neg hij.symm] at hj
    simp only [if_neg hil.symm] at hl
    linarith only [hj.1,hl.1]
  have hoff : (120243/25000 : ℝ) ≤ X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1 := by
    have h01 := hbox 0 1; have h02 := hbox 0 2
    have h10 := hbox 1 0; have h12 := hbox 1 2
    have h20 := hbox 2 0; have h21 := hbox 2 1
    norm_num [Fin.ext_iff] at h01 h02 h10 h12 h20 h21
    linarith only [h01.1,h02.1,h10.1,h12.1,h20.1,h21.1]
  have hrT : (16810527499/78618079880 : ℝ)^(p-2) ≤ (3758951328135787089/100000000000000000000 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_ge' (by norm_num : (0 : ℝ) ≤ (16810527499/78618079880 : ℝ))
      (by norm_num) (by norm_num : (0 : ℝ) ≤ (1089/512 : ℝ)) (by linarith only [hpa] : (1089/512 : ℝ) ≤ p-2)
    exact h.trans htailT
  have hrC : (844097733/3283435520 : ℝ)^(p-2) ≤ (2781021202655209377/50000000000000000000 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_ge' (by norm_num : (0 : ℝ) ≤ (844097733/3283435520 : ℝ))
      (by norm_num) (by norm_num : (0 : ℝ) ≤ (1089/512 : ℝ)) (by linarith only [hpa] : (1089/512 : ℝ) ≤ p-2)
    exact h.trans htailC
  have hNT : (16000564719851660311579186654910802068673/869470829408165011986676164245609536000 : ℝ)*(16810527499/78618079880 : ℝ)^(p-2) ≤ 1 := by
    nlinarith only [hrT]
  have hNC : (3939994420974305314955071458965795657381892113955789117/155620362366860595575078087607171874069419202350169600 : ℝ)*(844097733/3283435520 : ℝ)^(p-2) ≤ (101781167/50000000 : ℝ) := by
    nlinarith only [hrC]
  apply nonnegative_of_split_curvature_margins
    (p := p) (Klo := (151781167/100000000 : ℝ)) (Khi := (31/20 : ℝ)) (ell := (1856/3125 : ℝ)) (u := (249/400 : ℝ)) (v := (40081/50000 : ℝ)) (w := (16677/20000 : ℝ)) (U := (1020249/1000000 : ℝ)) (A := (700643/500000 : ℝ)) (J := (40081/25000 : ℝ)) (W0 := (120243/25000 : ℝ)) (m := (1856/3125 : ℝ)) (M := (16677/20000 : ℝ)) (r := (3559800541/5136300000 : ℝ)) (R := (477725709/654188000 : ℝ)) (L := (40081/25000 : ℝ)) (s := (49037/50000 : ℝ)) (t := (53689/50000 : ℝ)) (eta := (23993/100000 : ℝ)) (eps1 := (2847/1000 : ℝ)) (eps2 := (587/1000 : ℝ)) (gT := (736676522890363442261962164197781/54232106821696378083548075412640 : ℝ)) (gC := (124574093407567751406766686493129512671523738843/4853308374506018923401302599959203677222973552 : ℝ))
    (by linarith only [hpa]) (by linarith only [hKone]) hKlo.le hKhi
  all_goals first
    | exact hbox
    | exact hrows
    | exact htotal
    | exact hpairs
    | exact hoff
    | (norm_num at hNT ⊢; exact hNT)
    | (norm_num at hNC ⊢; exact hNC)
    | norm_num

end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hbox : ∀ j i, if j=i then -(249/400 : ℝ) ≤ X j i ∧ X j i ≤ -(1856/3125 : ℝ)
      else (40081/50000 : ℝ) ≤ X j i ∧ X j i ≤ (16677/20000 : ℝ)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by
  exact HlawkaSchatten.DiagonalCutoff4.box_nonnegative_w1260 p hpa hpb X hbox

#print axioms solution

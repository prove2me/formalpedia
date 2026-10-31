-- Prove2me | solution 1 for OAI.SKRatio.Calculus.ratio_cutoff_of_uniform_gradient
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:19:07.841425+00:00
-- url     : https://prove2.me/submissions/17e01fea-3e9b-4875-ac08-d53d34cb6ef1

import Mathlib
import Definitions.Def_SKRatio
import Definitions.Def_OAIQ024S009

section
-- module Solutions.OAIQ024_SK.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_FiniteChain_Spin
attribute [-instance] _root_.OAI.SKRatioGaussian.instNonemptyUnitBall
attribute [-simp] _root_.OAI.SKRatio.Calculus.abs_signConjugate _root_.OAI.SKRatio.Calculus.abs_spin _root_.OAI.SKRatio.Calculus.attempt_const _root_.OAI.SKRatio.Calculus.attempt_pow_const _root_.OAI.SKRatio.Calculus.continuousDistance_zero _root_.OAI.SKRatio.Calculus.continuousKernel_zero _root_.OAI.SKRatio.Calculus.field_reversal _root_.OAI.SKRatio.Calculus.generator_const _root_.OAI.SKRatio.Calculus.gibbsEuclideanEquiv_apply _root_.OAI.SKRatio.Calculus.gibbsMeanCLM_apply _root_.OAI.SKRatio.Calculus.halfDiff_const _root_.OAI.SKRatio.Calculus.halfDiff_replace _root_.OAI.SKRatio.Calculus.halfDiff_self _root_.OAI.SKRatio.Calculus.halfDiff_spin _root_.OAI.SKRatio.Calculus.lift_scalarEigenfunction _root_.OAI.SKRatio.Calculus.mass_reversal _root_.OAI.SKRatio.Calculus.norm_signedVector _root_.OAI.SKRatio.Calculus.plus_signProduct _root_.OAI.SKRatio.Calculus.replace_replace _root_.OAI.SKRatio.Calculus.replace_same _root_.OAI.SKRatio.Calculus.replace_self _root_.OAI.SKRatio.Calculus.reversal_reversal _root_.OAI.SKRatio.Calculus.semigroup_zero _root_.OAI.SKRatio.Calculus.signConjugate_twice _root_.OAI.SKRatio.Calculus.signProduct_plus _root_.OAI.SKRatio.Calculus.siteRefresh_const _root_.OAI.SKRatio.Calculus.spin_reversal _root_.OAI.SKRatio.Calculus.spin_sq _root_.OAI.SKRatio.Calculus.stationaryPairingCLM_apply _root_.OAI.SKRatio.Independent.coupling_zero _root_.OAI.SKRatio.Independent.mass_zero _root_.OAI.SKRatio.Independent.siteKernel_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter

namespace SKRatio

section HeatBath
variable {n : ℕ}

theorem siteKernel_nonneg (g : Disorder n) (i : Fin n) (x y : Spin n) :
    0 ≤ siteKernel g i x y := by
  unfold siteKernel
  have hx := mass_nonneg g 0 x
  have hf := mass_nonneg g 0 (flip i x)
  positivity

theorem siteKernel_stationary (g : Disorder n) (i : Fin n) (y : Spin n) :
    ∑ x, mass g 0 x * siteKernel g i x y = mass g 0 y := by
  simp_rw [siteKernel_balance g i _ y]
  rw [← Finset.mul_sum, sum_siteKernel, mul_one]

theorem transition_stochastic (g : Disorder n) :
    transition g ∈ Matrix.rowStochastic ℝ (Spin n) := by
  by_cases hn : n = 0
  · simp only [transition, hn, ↓reduceIte]
    exact (Matrix.rowStochastic ℝ (Spin n)).one_mem
  · rw [Matrix.mem_rowStochastic_iff_sum]
    simp only [transition, hn, ↓reduceIte]
    constructor
    · intro x y
      exact div_nonneg (Finset.sum_nonneg (fun i _ => siteKernel_nonneg g i x y))
        (Nat.cast_nonneg n)
    · intro x
      rw [← Finset.sum_div, Finset.sum_comm]
      simp [Nat.cast_ne_zero.mpr hn]

theorem transition_nonneg (g : Disorder n) (x y : Spin n) :
    0 ≤ transition g x y := (transition_stochastic g).1 x y

theorem transition_stationary (g : Disorder n) :
    (mass g 0) ᵥ* transition g = mass g 0 := by
  by_cases hn : n = 0
  · simp [transition, hn]
  · ext y
    simp only [Matrix.vecMul, dotProduct, transition, hn, ↓reduceIte,
      mul_div, ← Finset.sum_div, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp [siteKernel_stationary, Nat.cast_ne_zero.mpr hn]

theorem transition_pow_stochastic (g : Disorder n) (k : ℕ) :
    transition g ^ k ∈ Matrix.rowStochastic ℝ (Spin n) :=
  (Matrix.rowStochastic ℝ (Spin n)).pow_mem (transition_stochastic g) k

theorem transition_pow_stationary (g : Disorder n) (k : ℕ) :
    (mass g 0) ᵥ* (transition g ^ k) = mass g 0 := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, transition_stationary]

theorem siteKernel_update_pos (g : Disorder n) (i : Fin n) (x : Spin n) (b : Bool) :
    0 < siteKernel g i x (Function.update x i b) := by
  by_cases hb : b = x i
  · subst b
    simp only [Function.update_eq_self, siteKernel, Ne.symm (flip_ne i x),
      ↓reduceIte, add_zero]
    exact div_pos (mass_pos g 0 x) (add_pos (mass_pos g 0 x) (mass_pos g 0 (flip i x)))
  · have hb' : b = !(x i) := by cases b <;> cases h : x i <;> simp_all
    subst b
    change 0 < siteKernel g i x (flip i x)
    simp only [siteKernel, flip_ne, ↓reduceIte, zero_add]
    exact div_pos (mass_pos g 0 (flip i x))
      (add_pos (mass_pos g 0 x) (mass_pos g 0 (flip i x)))

theorem transition_update_pos (g : Disorder n) (i : Fin n) (x : Spin n) (b : Bool) :
    0 < transition g x (Function.update x i b) := by
  have hn : n ≠ 0 := ne_of_gt (Nat.zero_lt_of_lt i.isLt)
  simp only [transition, hn, ↓reduceIte]
  apply div_pos _ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
  exact (siteKernel_update_pos g i x b).trans_le
    (Finset.single_le_sum (fun j _ => siteKernel_nonneg g j x _) (Finset.mem_univ i))

theorem updatePath_succ (x y : Spin n) (k : ℕ) (hk : k < n) :
    updatePath x y (k + 1) =
      Function.update (updatePath x y k) ⟨k, hk⟩ (y ⟨k, hk⟩) := by
  ext i
  by_cases hi : i = ⟨k, hk⟩
  · subst i
    simp [updatePath]
  · have hval : (i : ℕ) ≠ k := fun h => hi (Fin.ext h)
    have hlt : (i : ℕ) < k + 1 ↔ (i : ℕ) < k := by omega
    simp [Function.update_of_ne hi, updatePath, hlt]

theorem transition_n_pos (g : Disorder n) (x y : Spin n) :
    0 < (transition g ^ n) x y := by
  have path_pos (k : ℕ) (hk : k ≤ n) :
      0 < (transition g ^ k) x (updatePath x y k) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hkn : k < n := by omega
      have hprev := ih (by omega)
      rw [pow_succ, Matrix.mul_apply]
      have hlast : 0 < transition g (updatePath x y k) (updatePath x y (k + 1)) := by
        rw [updatePath_succ x y k hkn]
        exact transition_update_pos g ⟨k, hkn⟩ _ _
      exact (mul_pos hprev hlast).trans_le
        (Finset.single_le_sum
          (fun z _ => mul_nonneg ((transition_pow_stochastic g k).1 x z)
            (transition_nonneg g z _)) (Finset.mem_univ _))
  simpa using path_pos n le_rfl

end HeatBath

section FiniteTV
variable {α : Type*} [Fintype α]

theorem totalVariation_nonneg (p q : α → ℝ) : 0 ≤ totalVariation p q := by
  unfold totalVariation
  positivity

theorem totalVariation_le_one (p q : α → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hp1 : ∑ x, p x = 1) (hq1 : ∑ x, q x = 1) :
    totalVariation p q ≤ 1 := by
  calc
    totalVariation p q ≤ (1 / 2 : ℝ) * ∑ x, (p x + q x) := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x _ => ?_)) (by norm_num)
      simpa [abs_of_nonneg (hp x), abs_of_nonneg (hq x)] using abs_sub (p x) (q x)
    _ = 1 := by rw [Finset.sum_add_distrib, hp1, hq1]; norm_num

variable [DecidableEq α]

theorem totalVariation_dirac (q : α → ℝ) (hq : ∀ x, 0 ≤ q x)
    (hq1 : ∑ x, q x = 1) (x : α) :
    totalVariation ((1 : Matrix α α ℝ) x) q = 1 - q x := by
  have hqx : q x ≤ 1 := by
    rw [← hq1]
    exact Finset.single_le_sum (fun y _ => hq y) (Finset.mem_univ x)
  have summand (y : α) :
      |(1 : Matrix α α ℝ) x y - q y| = q y + if y = x then 1 - 2 * q x else 0 := by
    by_cases h : y = x
    · subst y
      simp only [Matrix.one_apply_eq, ↓reduceIte, abs_of_nonneg (sub_nonneg.mpr hqx)]
      ring
    · simp [Matrix.one_apply_ne (Ne.symm h), h, abs_of_nonneg (hq y)]
  simp only [totalVariation, summand, Finset.sum_add_distrib, hq1,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  ring

theorem totalVariation_minorization (A : Matrix α α ℝ)
    (hA : A ∈ Matrix.rowStochastic ℝ α) (p q : α → ℝ)
    (hpq : ∑ x, p x = ∑ x, q x) (c : ℝ) (hc : ∀ x y, c ≤ A x y) :
    totalVariation (p ᵥ* A) (q ᵥ* A) ≤
      (1 - (Fintype.card α : ℝ) * c) * totalVariation p q := by
  have hdiff (y : α) : (p ᵥ* A) y - (q ᵥ* A) y =
      ∑ x, (p x - q x) * (A x y - c) := by
    simp only [Matrix.vecMul, dotProduct, mul_sub, sub_mul, Finset.sum_sub_distrib,
      ← Finset.sum_mul, hpq]
    ring
  have hrow (x : α) : ∑ y, (A x y - c) = 1 - (Fintype.card α : ℝ) * c := by
    simp only [Finset.sum_sub_distrib, Matrix.sum_row_of_mem_rowStochastic hA,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have habs (y : α) : |(p ᵥ* A) y - (q ᵥ* A) y| ≤
      ∑ x, |p x - q x| * (A x y - c) := by
    rw [hdiff]
    calc
      |∑ x, (p x - q x) * (A x y - c)| ≤ ∑ x, |(p x - q x) * (A x y - c)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = _ := Finset.sum_congr rfl (fun x _ => by
        rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hc x y))])
  calc
    totalVariation (p ᵥ* A) (q ᵥ* A) ≤
        (1 / 2 : ℝ) * ∑ y, ∑ x, |p x - q x| * (A x y - c) := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun y _ => habs y)) (by norm_num)
    _ = (1 / 2 : ℝ) * ∑ x,
        |p x - q x| * (1 - (Fintype.card α : ℝ) * c) := by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, hrow]
    _ = (1 - (Fintype.card α : ℝ) * c) * totalVariation p q := by
      rw [← Finset.sum_mul]
      unfold totalVariation
      ring

theorem totalVariation_contract (A : Matrix α α ℝ)
    (hA : A ∈ Matrix.rowStochastic ℝ α) (p q : α → ℝ)
    (hpq : ∑ x, p x = ∑ x, q x) :
    totalVariation (p ᵥ* A) (q ᵥ* A) ≤ totalVariation p q := by
  simpa using totalVariation_minorization A hA p q hpq 0 hA.1

theorem exists_geometric_block_bound [Nonempty α] (A : Matrix α α ℝ)
    (hA : A ∈ Matrix.rowStochastic ℝ α) (π : α → ℝ)
    (hπ : ∀ x, 0 ≤ π x) (hπ1 : ∑ x, π x = 1)
    (m : ℕ) (hm : ∀ x y, 0 < (A ^ m) x y) (hstation : π ᵥ* (A ^ m) = π) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧
      ∀ k : ℕ, ∀ x, totalVariation ((A ^ (m * k)) x) π ≤ r ^ k := by
  classical
  let c : ℝ := Finset.univ.inf' Finset.univ_nonempty
    (fun xy : α × α => (A ^ m) xy.1 xy.2)
  have hc : 0 < c := (Finset.lt_inf'_iff _).mpr (fun xy _ => hm xy.1 xy.2)
  have hcA (x y : α) : c ≤ (A ^ m) x y :=
    Finset.inf'_le _ (Finset.mem_univ (x, y))
  have hAm := (Matrix.rowStochastic ℝ α).pow_mem hA m
  let r : ℝ := 1 - (Fintype.card α : ℝ) * c
  have hr0 : 0 ≤ r := by
    have H : (Fintype.card α : ℝ) * c ≤ 1 := by
      calc
        (Fintype.card α : ℝ) * c = ∑ _y : α, c := by simp
        _ ≤ ∑ y, (A ^ m) (Classical.arbitrary α) y := Finset.sum_le_sum (fun y _ => hcA _ y)
        _ = 1 := Matrix.sum_row_of_mem_rowStochastic hAm _
    exact sub_nonneg.mpr H
  have hr1 : r < 1 := by
    have hcard : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
    dsimp [r]
    linarith [mul_pos hcard hc]
  refine ⟨r, hr0, hr1, ?_⟩
  intro k
  induction k with
  | zero =>
    intro x
    simp only [Nat.mul_zero, pow_zero]
    have hI := (Matrix.rowStochastic ℝ α).one_mem
    exact totalVariation_le_one _ _ (hI.1 x) hπ
      (Matrix.sum_row_of_mem_rowStochastic hI x) hπ1
  | succ k ih =>
    intro x
    rw [Nat.mul_succ, pow_add, Matrix.mul_apply_eq_vecMul]
    have hAk := (Matrix.rowStochastic ℝ α).pow_mem hA (m * k)
    have hequal : (∑ y, (A ^ (m * k)) x y) = ∑ y, π y := by
      rw [Matrix.sum_row_of_mem_rowStochastic hAk, hπ1]
    calc
      totalVariation ((A ^ (m * k)) x ᵥ* (A ^ m)) π =
          totalVariation ((A ^ (m * k)) x ᵥ* (A ^ m)) (π ᵥ* (A ^ m)) := by rw [hstation]
      _ ≤ r * totalVariation ((A ^ (m * k)) x) π :=
        totalVariation_minorization (A ^ m) hAm _ _ hequal c hcA
      _ ≤ r * r ^ k := mul_le_mul_of_nonneg_left (ih x) hr0
      _ = r ^ (k + 1) := by rw [pow_succ, mul_comm]

end FiniteTV

section MixingTime
variable {n : ℕ}

theorem tv_le_discreteDistance (g : Disorder n) (k : ℕ) (x : Spin n) :
    totalVariation ((transition g ^ k) x) (mass g 0) ≤ discreteDistance g k := by
  unfold discreteDistance
  exact Finset.le_sup' (fun z : Spin n => totalVariation ((transition g ^ k) z) (mass g 0))
    (Finset.mem_univ x)

end MixingTime
end SKRatio
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_Interaction
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
attribute [-simp] _root_.OAI.SKRatio.Calculus.abs_signConjugate _root_.OAI.SKRatio.Calculus.abs_spin _root_.OAI.SKRatio.Calculus.attempt_const _root_.OAI.SKRatio.Calculus.attempt_pow_const _root_.OAI.SKRatio.Calculus.continuousKernel_zero _root_.OAI.SKRatio.Calculus.field_reversal _root_.OAI.SKRatio.Calculus.generator_const _root_.OAI.SKRatio.Calculus.gibbsEuclideanEquiv_apply _root_.OAI.SKRatio.Calculus.gibbsMeanCLM_apply _root_.OAI.SKRatio.Calculus.lift_scalarEigenfunction _root_.OAI.SKRatio.Calculus.mass_reversal _root_.OAI.SKRatio.Calculus.mean_weight_plus _root_.OAI.SKRatio.Calculus.norm_signedVector _root_.OAI.SKRatio.Calculus.plus_signProduct _root_.OAI.SKRatio.Calculus.reversal_reversal _root_.OAI.SKRatio.Calculus.signConjugate_twice _root_.OAI.SKRatio.Calculus.signProduct_plus _root_.OAI.SKRatio.Calculus.siteRefresh_const _root_.OAI.SKRatio.Calculus.spin_reversal _root_.OAI.SKRatio.Calculus.stationaryPairingCLM_apply _root_.OAI.SKRatio.Independent.mass_zero _root_.OAI.SKRatio.Independent.siteKernel_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap
namespace SKRatio.Calculus

theorem halfDiff_mul {n : ℕ} (i : Fin n) (f g : Spin n → ℝ) (x : Spin n) :
    halfDiff i (fun y => f y * g y) x =
      f x * halfDiff i g x + g x * halfDiff i f x -
        2 * spin x i * halfDiff i f x * halfDiff i g x := by
  have hx : replace x i (x i) = x := replace_self x i
  cases h : x i <;> simp only [h] at hx
  · simp only [halfDiff, spin, h, Bool.false_eq_true, ↓reduceIte]
    rw [hx]
    ring
  · simp only [halfDiff, spin, h, ↓reduceIte]
    rw [hx]
    ring

theorem halfDiff_sum {n : ℕ} {α : Type*} [Fintype α] (i : Fin n)
    (f : α → Spin n → ℝ) (x : Spin n) :
    halfDiff i (fun y => ∑ a, f a y) x = ∑ a, halfDiff i (f a) x := by
  simp only [halfDiff, sub_div, Finset.sum_sub_distrib, Finset.sum_div]

lemma generator_mul {n : ℕ} (J : Interaction n) (f g : Observables n) (x : Spin n) :
    generator J (fun y => f y * g y) x =
      f x * generator J g x + g x * generator J f x +
        2 * ∑ i, (1 - mean J x i * spin x i) * halfDiff i f x * halfDiff i g x := by
  simp only [generator, halfDiff_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hx := spin_sq x i
  linear_combination 2 * halfDiff i f x * halfDiff i g x * hx

lemma semigroup_hasDerivAt {n : ℕ} (J : Interaction n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => semigroup J s)
      (semigroup J t * generatorCLM J) t :=
  hasDerivAt_exp_smul_const (generatorCLM J) t

lemma semigroup_hasDerivAt' {n : ℕ} (J : Interaction n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => semigroup J s)
      (generatorCLM J * semigroup J t) t :=
  hasDerivAt_exp_smul_const' (generatorCLM J) t

lemma semigroup_apply_hasDerivAt' {n : ℕ} (J : Interaction n) (f : Observables n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => semigroup J s f) (generator J (semigroup J t f)) t := by
  simpa only [mul_apply_eq_comp, map_zero, add_zero, generatorCLM, generatorLM,
    LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk] using
    (semigroup_hasDerivAt' J t).clm_apply (hasDerivAt_const t f)

lemma semigroup_continuous {n : ℕ} (J : Interaction n) :
    Continuous (fun s : ℝ => semigroup J s) := by
  have hd : Differentiable ℝ (fun s : ℝ => semigroup J s) :=
    fun t => (semigroup_hasDerivAt J t).differentiableAt
  exact hd.continuous

lemma generator_square {n : ℕ} (J : Interaction n) (f : Observables n) :
    generator J (fun x => f x ^ 2) =
      fun x => 2 * f x * generator J f x + jumpEnergy J f x := by
  funext x
  simpa only [pow_two, mul_assoc, ← two_mul, jumpEnergy] using generator_mul J f f x

lemma field_flip {n : ℕ} (J : Interaction n) (hdiag : ∀ i, J i i = 0)
    (x : Spin n) (i : Fin n) : field J (flip i x) i = field J x i := by
  simp only [field, spin_flip, mul_sub, Finset.sum_sub_distrib]
  simp [mul_ite, hdiag]

lemma variance_density {n : ℕ} (J : Interaction n) (f : Observables n) (x : Spin n) :
    generator J (fun y => f y ^ 2) x - 2 * f x * generator J f x =
      2 * weightedGradient J f x := by
  rw [generator_square]
  simp only [jumpEnergy, weightedGradient, gradientWeight, mul_comm (mean J x _)]
  ring

lemma halfDiff_flow_hasDerivAt {n : ℕ} (J : Interaction n) (f : Observables n)
    (i : Fin n) (x : Spin n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => halfDiff i (semigroup J s f) x)
      (halfDiff i (generator J (semigroup J t f)) x) t := by
  have h := semigroup_apply_hasDerivAt' J f t
  exact ((hasDerivAt_pi.mp h (replace x i true)).sub
    (hasDerivAt_pi.mp h (replace x i false))).div_const 2

lemma unweightedGradient_hasDerivAt {n : ℕ} (J : Interaction n) (f : Observables n)
    (x : Spin n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => unweightedGradient (semigroup J s f) x)
      (∑ i, 2 * halfDiff i (semigroup J t f) x *
        halfDiff i (generator J (semigroup J t f)) x) t := by
  have hs := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => (halfDiff_flow_hasDerivAt J f i x t).pow 2)
  simpa only [unweightedGradient, Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.pow_apply] using hs

end SKRatio.Calculus
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_PlusSpin
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap
namespace SKRatio.Calculus

open Real Set

lemma hasDerivAt_tanh (y : ℝ) : HasDerivAt tanh (1 - tanh y ^ 2) y := by
  convert! (Real.hasDerivAt_sinh y).div (Real.hasDerivAt_cosh y) (cosh_pos y).ne' using 1
  · ext x
    exact tanh_eq_sinh_div_cosh x
  · rw [tanh_eq_sinh_div_cosh]
    field_simp

lemma scalarVariance_pos (h : ℝ) : 0 < scalarVariance h :=
  sub_pos.mpr (Real.tanh_sq_lt_one h)

lemma gradientWeight_pos {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) :
    0 < gradientWeight J x i := by
  cases hi : x i
  · have h := Real.neg_one_lt_tanh (field J x i)
    simp only [gradientWeight, spin, hi, Bool.false_eq_true, ↓reduceIte, neg_mul,
      one_mul, sub_neg_eq_add, mean]
    linarith
  · simpa only [gradientWeight, spin, hi, ↓reduceIte, one_mul, mean] using
      sub_pos.mpr (Real.tanh_lt_one (field J x i))

end SKRatio.Calculus
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_FiniteChain_Mean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter
namespace SKRatio
namespace FiniteLaw
variable {α : Type*} [Fintype α]

theorem variance_eq (p f : α → ℝ) (hp1 : ∑ x, p x = 1) :
    variance p f = mean p (fun x => f x ^ 2) - mean p f ^ 2 := by
  have h (x : α) : p x * (f x - mean p f) ^ 2 =
      p x * f x ^ 2 - 2 * mean p f * (p x * f x) + mean p f ^ 2 * p x := by ring
  simp only [variance, h, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, hp1, mul_one]
  simp only [mean]
  ring

theorem common_mass (p q : α → ℝ) (hp1 : ∑ x, p x = 1) (hq1 : ∑ x, q x = 1) :
    ∑ x, min (p x) (q x) = 1 - totalVariation p q := by
  have h (x : α) : min (p x) (q x) = (p x + q x - |p x - q x|) / 2 := by
    rcases le_total (p x) (q x) with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
  simp only [h, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib, hp1, hq1,
    totalVariation]
  ring

theorem common_mass_square (p q f : α → ℝ) (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hp1 : ∑ x, p x = 1) (hq1 : ∑ x, q x = 1) :
    (1 - totalVariation p q) * (mean p f - mean q f) ^ 2 ≤
      2 * variance p f + 2 * variance q f := by
  rw [← common_mass p q hp1 hq1, Finset.sum_mul]
  calc
    _ ≤ ∑ x, (2 * (p x * (f x - mean p f) ^ 2) +
        2 * (q x * (f x - mean q f) ^ 2)) := by
      apply Finset.sum_le_sum
      intro x _
      have hpoint : (mean p f - mean q f) ^ 2 ≤
          2 * (f x - mean p f) ^ 2 + 2 * (f x - mean q f) ^ 2 := by nlinarith [sq_nonneg (2 * f x - mean p f - mean q f)]
      have hmul := mul_le_mul_of_nonneg_left hpoint (le_min (hp x) (hq x))
      have hpbound := mul_le_mul_of_nonneg_right (min_le_left (p x) (q x)) (sq_nonneg (f x - mean p f))
      have hqbound := mul_le_mul_of_nonneg_right (min_le_right (p x) (q x)) (sq_nonneg (f x - mean q f))
      nlinarith only [hmul, hpbound, hqbound]
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum, variance]

end FiniteLaw
end SKRatio
end
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_SignedVector
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
attribute [-simp] _root_.OAI.SKRatio.Calculus.continuousDistance_zero _root_.OAI.SKRatio.Calculus.continuousKernel_zero _root_.OAI.SKRatio.Calculus.field_reversal _root_.OAI.SKRatio.Calculus.gibbsEuclideanEquiv_apply _root_.OAI.SKRatio.Calculus.gibbsMeanCLM_apply _root_.OAI.SKRatio.Calculus.lift_scalarEigenfunction _root_.OAI.SKRatio.Calculus.mass_reversal _root_.OAI.SKRatio.Calculus.reversal_reversal _root_.OAI.SKRatio.Calculus.spin_reversal _root_.OAI.SKRatio.Calculus.stationaryPairingCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap
namespace SKRatio.Calculus
open Real Set

theorem generator_siteRefresh {n : ℕ} (J : Interaction n) (f : Observables n)
    (x : Spin n) : generator J f x = ∑ i, (siteRefresh J i f x - f x) := by
  apply Finset.sum_congr rfl
  intro i _
  have hx : replace x i (x i) = x := replace_self x i
  cases hi : x i <;> simp only [hi] at hx
  · simp only [halfDiff, spin, hi, Bool.false_eq_true, ↓reduceIte, siteRefresh]
    rw [hx]
    ring
  · simp only [halfDiff, spin, hi, ↓reduceIte, siteRefresh]
    rw [hx]
    ring

theorem attempt_apply_of_pos {n : ℕ} (hn : 0 < n) (J : Interaction n)
    (f : Observables n) (x : Spin n) :
    attemptLM J f x = (∑ i, siteRefresh J i f x) / (n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  change f x + (n : ℝ)⁻¹ * generator J f x = _
  rw [generator_siteRefresh, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem siteRefresh_nonneg {n : ℕ} (J : Interaction n) (i : Fin n)
    (f : Observables n) (hf : ∀ x, 0 ≤ f x) (x : Spin n) :
    0 ≤ siteRefresh J i f x := by
  have hm1 : -1 ≤ mean J x i := le_of_lt (Real.neg_one_lt_tanh _)
  have hm2 : mean J x i ≤ 1 := le_of_lt (Real.tanh_lt_one _)
  exact add_nonneg (mul_nonneg (by linarith) (hf _))
    (mul_nonneg (by linarith) (hf _))

theorem attempt_nonneg {n : ℕ} (J : Interaction n) (f : Observables n)
    (hf : ∀ x, 0 ≤ f x) (x : Spin n) : 0 ≤ attemptLM J f x := by
  by_cases hn : n = 0
  · subst n
    simpa [attemptLM] using hf x
  · rw [attempt_apply_of_pos (Nat.pos_of_ne_zero hn)]
    exact div_nonneg (Finset.sum_nonneg (fun _ _ => siteRefresh_nonneg J _ f hf x))
      (Nat.cast_nonneg n)

theorem attempt_pow_nonneg {n : ℕ} (J : Interaction n) (k : ℕ) (f : Observables n)
    (hf : ∀ x, 0 ≤ f x) (x : Spin n) : 0 ≤ (attemptLM J ^ k) f x := by
  induction k generalizing x with
  | zero => simpa using hf x
  | succ k ih =>
    simp only [pow_succ', mul_apply_eq_comp]
    exact attempt_nonneg J _ ih x

theorem exp_apply_hasSum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) (f : E) :
    HasSum (fun k : ℕ => (k.factorial : ℝ)⁻¹ • ((A ^ k) f))
      (NormedSpace.exp A f) := by
  simpa only [NormedSpace.expSeries_apply_eq, ContinuousLinearMap.apply_apply,
    smul_apply] using
    (ContinuousLinearMap.apply ℝ E f).hasSum
      (NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) A)

theorem exp_apply_of_apply_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (A : E →L[ℝ] E) (f : E)
    (h : A f = 0) : NormedSpace.exp A f = f := by
  have hp (k : ℕ) : (A ^ (k + 1)) f = 0 := by
    induction k with
    | zero => simpa using h
    | succ k ih => rw [pow_succ', mul_apply_eq_comp, ih, map_zero]
  have hs : HasSum (fun k : ℕ => (k.factorial : ℝ)⁻¹ • ((A ^ k) f)) f := by
    convert hasSum_ite_eq 0 f using 1
    all_goals try with_reducible_and_instances rfl
    funext k
    cases k with
    | zero => simp
    | succ k => simp [hp]
  exact (exp_apply_hasSum A f).unique hs

@[simp] theorem semigroup_const {n : ℕ} (J : Interaction n) (t a : ℝ) :
    semigroup J t (fun _ => a) = fun _ => a := by
  apply exp_apply_of_apply_eq_zero
  funext x
  change t * generator J (fun _ => a) x = 0
  simp

theorem exp_smul_identity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (a : ℝ) :
    NormedSpace.exp (a • (1 : E →L[ℝ] E)) = Real.exp a • (1 : E →L[ℝ] E) := by
  simpa only [Algebra.algebraMap_eq_smul_one, ← Real.exp_eq_exp_ℝ] using
    (NormedSpace.algebraMap_exp_comm (𝔸 := E →L[ℝ] E) a).symm

theorem semigroup_uniformization {n : ℕ} (hn : 0 < n) (J : Interaction n) (t : ℝ) :
    semigroup J t = Real.exp (-(n : ℝ) * t) •
      NormedSpace.exp (((n : ℝ) * t) • attemptLM J) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have heq : t • generatorCLM J =
      (-(n : ℝ) * t) • (1 : Observables n →L[ℝ] Observables n) +
        ((n : ℝ) * t) • attemptLM J := by
    unfold attemptLM
    simp only [smul_add, smul_smul]
    have hc : ((n : ℝ) * t) * (n : ℝ)⁻¹ = t := by field_simp
    rw [hc]
    module
  let : NormedAlgebra ℚ (Observables n →L[ℝ] Observables n) :=
    NormedAlgebra.restrictScalars ℚ ℝ _
  unfold semigroup
  rw [heq, NormedSpace.exp_add_of_commute
    (((Commute.one_left (attemptLM J)).smul_left _).smul_right _),
    exp_smul_identity, smul_mul_assoc, one_mul]

theorem semigroup_nonneg {n : ℕ} (J : Interaction n) (t : ℝ) (ht : 0 ≤ t)
    (f : Observables n) (hf : ∀ x, 0 ≤ f x) (x : Spin n) :
    0 ≤ semigroup J t f x := by
  by_cases hn : n = 0
  · subst n
    have hL : generatorCLM J = 0 := by
      ext f x
      simp [generatorCLM, generatorLM, generator]
    simp only [semigroup, hL, smul_zero, NormedSpace.exp_zero,
      one_apply_eq_self]
    exact hf x
  · rw [semigroup_uniformization (Nat.pos_of_ne_zero hn)]
    simp only [smul_apply, Pi.smul_apply, smul_eq_mul]
    apply mul_nonneg (le_of_lt (Real.exp_pos _))
    have hs := Pi.hasSum.mp (exp_apply_hasSum (((n : ℝ) * t) • attemptLM J) f) x
    apply HasSum.nonneg _ hs
    intro k
    simp only [smul_pow, smul_apply, Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (mul_nonneg (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) ht) _)
        (attempt_pow_nonneg J k f hf x))

theorem continuousKernel_nonneg {n : ℕ} (J : Interaction n) (t : ℝ) (ht : 0 ≤ t)
    (x y : Spin n) : 0 ≤ continuousKernel J t x y := by
  exact semigroup_nonneg J t ht _ (fun _ => by split_ifs <;> norm_num) x

theorem continuousKernel_sum {n : ℕ} (J : Interaction n) (t : ℝ) (x : Spin n) :
    ∑ y, continuousKernel J t x y = 1 := by
  have eq_one : (∑ y : Spin n, fun z => if z = y then (1 : ℝ) else 0) =
      fun _ : Spin n => (1 : ℝ) := by
    funext z
    simp
  unfold continuousKernel
  rw [← Finset.sum_apply, ← map_sum, eq_one, semigroup_const]

theorem attempt_eq_transition {n : ℕ} (g : Disorder n) (f : Observables n) :
    attemptLM (coupling g) f = transition g *ᵥ f := by
  funext x
  by_cases hn : n = 0
  · subst n
    simp [attemptLM, transition]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  change f x + (n : ℝ)⁻¹ * generator (coupling g) f x = _
  rw [generator_eq_transition]
  simp only [← mul_assoc, inv_mul_cancel₀ hn', one_mul]
  change f x + ((transition g *ᵥ f) x - f x) = (transition g *ᵥ f) x
  ring

theorem attempt_pow_eq_transition_pow {n : ℕ} (g : Disorder n) (k : ℕ)
    (f : Observables n) : (attemptLM (coupling g)^k) f = transition g^k *ᵥ f := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', mul_apply_eq_comp, ih, attempt_eq_transition,
      Matrix.mulVec_mulVec]

theorem semigroup_add {n : ℕ} (J : Interaction n) (s t : ℝ) :
    semigroup J (s+t) = semigroup J s * semigroup J t := by
  let : NormedAlgebra ℚ (Observables n →L[ℝ] Observables n) :=
    NormedAlgebra.restrictScalars ℚ ℝ _
  unfold semigroup
  rw [add_smul, NormedSpace.exp_add_of_commute
    (((Commute.refl (generatorCLM J)).smul_left _).smul_right _)]

theorem semigroup_mono {n : ℕ} (J : Interaction n) {t : ℝ} (ht : 0 ≤ t)
    (f h : Observables n) (hfh : ∀ x, f x ≤ h x) (x : Spin n) :
    semigroup J t f x ≤ semigroup J t h x := by
  have hn := semigroup_nonneg J t ht (h-f) (fun x => sub_nonneg.mpr (hfh x)) x
  simpa only [map_sub, Pi.sub_apply, sub_nonneg] using hn

theorem semigroup_abs_le {n : ℕ} (J : Interaction n) {t : ℝ} (ht : 0 ≤ t)
    (f : Observables n) {B : ℝ} (hf : ∀ x, |f x| ≤ B) (x : Spin n) :
    |semigroup J t f x| ≤ B := by
  have hu := semigroup_mono J ht f (fun _ => B) (fun x => (abs_le.mp (hf x)).2) x
  have hl := semigroup_mono J ht (fun _ => -B) f (fun x => (abs_le.mp (hf x)).1) x
  simp only [semigroup_const] at hu hl
  exact abs_le.mpr ⟨hl,hu⟩

theorem observable_basis {n : ℕ} (f : Observables n) :
    f = ∑ y : Spin n, f y • (fun z => if z = y then (1:ℝ) else 0) := by
  funext x
  simp

theorem semigroup_eq_kernel {n : ℕ} (J : Interaction n) (t : ℝ)
    (f : Observables n) (x : Spin n) :
    semigroup J t f x = FiniteLaw.mean (continuousKernel J t x) f := by
  conv_lhs => rw [observable_basis f]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    FiniteLaw.mean, continuousKernel]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem continuousKernel_add {n : ℕ} (J : Interaction n) (s t : ℝ) :
    continuousKernel J (s+t) =
      (continuousKernel J s : Matrix (Spin n) (Spin n) ℝ) * continuousKernel J t := by
  funext x y
  unfold continuousKernel
  rw [semigroup_add, mul_apply_eq_comp, semigroup_eq_kernel]
  rfl

theorem continuousKernel_poisson_hasSum {n : ℕ} (hn : 0 < n) (g : Disorder n)
    (t : ℝ) (x y : Spin n) :
    HasSum (fun k : ℕ => Real.exp (-(n:ℝ)*t) * ((n:ℝ)*t)^k /
      (k.factorial:ℝ) * (transition g^k) x y)
      (continuousKernel (coupling g) t x y) := by
  have hs := (Pi.hasSum.mp (exp_apply_hasSum (((n:ℝ)*t) • attemptLM (coupling g))
    (fun z => if z = y then (1:ℝ) else 0)) x).mul_left (Real.exp (-(n:ℝ)*t))
  simp only [smul_pow, smul_apply, Pi.smul_apply, smul_eq_mul,
    attempt_pow_eq_transition_pow, Matrix.mulVec, dotProduct,
    mul_ite, mul_one, mul_zero, Fintype.sum_ite_eq'] at hs
  rw [continuousKernel, semigroup_uniformization hn]
  have heq : (fun k : ℕ => Real.exp (-(n:ℝ)*t) * ((n:ℝ)*t)^k /
      (k.factorial:ℝ) * (transition g^k) x y) =
      (fun k : ℕ => Real.exp (-(n:ℝ)*t) * ((k.factorial:ℝ)⁻¹ *
        (((n:ℝ)*t)^k * (transition g^k) x y))) := by
    funext k
    ring
  rw [heq]
  exact hs

end SKRatio.Calculus
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_FiniteChain_VarianceNonneg
attribute [-simp] _root_.OAI.SKRatio.Calculus.gibbsMeanCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter
namespace SKRatio.FiniteLaw
variable {α : Type*} [Fintype α]

theorem submass_centered_mean (p ρ f : α → ℝ)
    (hρ : ∀ x, 0 ≤ ρ x) (hρp : ∀ x, ρ x ≤ p x) :
    |mean ρ (fun x => f x - mean p f)| ≤
      Real.sqrt (∑ x, ρ x) * Real.sqrt (variance p f) := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun x => Real.sqrt (ρ x)) (fun x => Real.sqrt (ρ x) * |f x - mean p f|)
  simp only [mul_pow, Real.sq_sqrt (hρ _), sq_abs,
    ← mul_assoc, Real.mul_self_sqrt (hρ _)] at hcs
  calc
    |mean ρ (fun x => f x - mean p f)| ≤ ∑ x, |ρ x * (f x - mean p f)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, ρ x * |f x - mean p f| := by
      apply Finset.sum_congr rfl
      intro x _
      rw [abs_mul, abs_of_nonneg (hρ x)]
    _ ≤ Real.sqrt (∑ x, ρ x) * Real.sqrt (∑ x, ρ x * (f x - mean p f) ^ 2) := hcs
    _ ≤ Real.sqrt (∑ x, ρ x) * Real.sqrt (variance p f) := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      apply Real.sqrt_le_sqrt
      exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_right (hρp x) (sq_nonneg _))

theorem common_mass_means (p q f : α → ℝ) (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hp1 : ∑ x, p x = 1) (hq1 : ∑ x, q x = 1)
    {ε : ℝ} (hε : 0 < ε) (hTV : totalVariation p q ≤ 1 - ε) :
    |mean p f - mean q f| ≤
      (Real.sqrt (variance p f) + Real.sqrt (variance q f)) / Real.sqrt ε := by
  let ρ := fun x => min (p x) (q x)
  let c : ℝ := ∑ x, ρ x
  have hρ : ∀ x, 0 ≤ ρ x := fun x => le_min (hp x) (hq x)
  have hpmean := submass_centered_mean p ρ f hρ (fun x => min_le_left _ _)
  have hqmean := submass_centered_mean q ρ f hρ (fun x => min_le_right _ _)
  have heq : c * (mean p f - mean q f) =
      mean ρ (fun x => f x - mean q f) - mean ρ (fun x => f x - mean p f) := by
    simp only [mean, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, c]
    ring
  have hc : ε ≤ c := by
    dsimp only [c, ρ]
    rw [common_mass p q hp1 hq1]
    linarith only [hTV]
  have hc0 : 0 < c := hε.trans_le hc
  have htriangle : c * |mean p f - mean q f| ≤
      Real.sqrt c * (Real.sqrt (variance p f) + Real.sqrt (variance q f)) := by
    calc
      c * |mean p f - mean q f| = |c * (mean p f - mean q f)| := by
        rw [abs_mul, abs_of_pos hc0]
      _ ≤ |mean ρ (fun x => f x - mean q f)| + |mean ρ (fun x => f x - mean p f)| := by
        rw [heq]
        exact abs_sub _ _
      _ ≤ Real.sqrt c * Real.sqrt (variance q f) + Real.sqrt c * Real.sqrt (variance p f) :=
        add_le_add hqmean hpmean
      _ = _ := by ring
  have hb : Real.sqrt c * |mean p f - mean q f| ≤
      Real.sqrt (variance p f) + Real.sqrt (variance q f) := by
    apply (mul_le_mul_iff_right₀ (Real.sqrt_pos.mpr hc0)).mp
    simpa only [← mul_assoc, Real.mul_self_sqrt hc0.le] using htriangle
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hε)).mpr
  calc
    |mean p f - mean q f| * Real.sqrt ε ≤ |mean p f - mean q f| * Real.sqrt c :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hc) (abs_nonneg _)
    _ ≤ _ := by simpa only [mul_comm] using hb

theorem totalVariation_le_of_tests (p q : α → ℝ) {B : ℝ}
    (h : ∀ f : α → ℝ, (∀ x, |f x| ≤ 1) → |mean p f - mean q f| ≤ 2 * B) :
    totalVariation p q ≤ B := by
  let f : α → ℝ := fun x => if 0 ≤ p x - q x then 1 else -1
  have hf : ∀ x, |f x| ≤ 1 := by
    intro x
    dsimp only [f]
    split_ifs <;> norm_num
  have hprod (x : α) : (p x - q x) * f x = |p x - q x| := by
    dsimp only [f]
    split_ifs with h
    · rw [mul_one, abs_of_nonneg h]
    · rw [mul_neg_one, abs_of_neg (lt_of_not_ge h)]
  have hid : mean p f - mean q f = 2 * totalVariation p q := by
    simp only [mean, ← Finset.sum_sub_distrib, ← sub_mul, hprod, totalVariation]
    ring
  have hbound := h f hf
  rw [hid, abs_of_nonneg (mul_nonneg (by norm_num) (totalVariation_nonneg p q))] at hbound
  linarith only [hbound]

end SKRatio.FiniteLaw

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_FiniteChain_MeanMulVec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter
namespace SKRatio
namespace FiniteLaw
variable {α : Type*} [Fintype α]

theorem mean_mulVec (p : α → ℝ) (A : Matrix α α ℝ) (f : α → ℝ) :
    mean p (A *ᵥ f) = mean (p ᵥ* A) f := by
  simp only [mean, Matrix.mulVec, Matrix.vecMul, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

end FiniteLaw

end SKRatio

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_GibbsMeanCLM
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
attribute [-simp] _root_.OAI.SKRatio.Calculus.continuousKernel_zero _root_.OAI.SKRatio.Calculus.field_reversal _root_.OAI.SKRatio.Calculus.gibbsEuclideanEquiv_apply _root_.OAI.SKRatio.Calculus.lift_scalarEigenfunction _root_.OAI.SKRatio.Calculus.mass_reversal _root_.OAI.SKRatio.Calculus.reversal_reversal _root_.OAI.SKRatio.Calculus.spin_reversal _root_.OAI.SKRatio.Calculus.stationaryPairingCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap
namespace SKRatio.Calculus
open Real Set

lemma gibbsMean_generator {n : ℕ} (g : Disorder n) (f : Observables n) :
    gibbsMeanCLM g (generator (coupling g) f) = 0 := by
  have heq : generator (coupling g) f = (n:ℝ) • (transition g *ᵥ f - f) := by
    funext x
    exact generator_eq_transition g f x
  rw [heq, map_smul, map_sub]
  simp only [gibbsMeanCLM_apply, FiniteLaw.mean_mulVec, transition_stationary, sub_self,
    smul_zero]

lemma functional_exp_invariant {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) (T : E →L[ℝ] ℝ)
    (h : ∀ f, T (A f) = 0) (f : E) : T (NormedSpace.exp A f) = T f := by
  have hp (k : ℕ) : T ((A^(k+1)) f) = 0 := by
    rw [pow_succ', mul_apply_eq_comp, h]
  have hs := T.hasSum (exp_apply_hasSum A f)
  have eqs : (fun k : ℕ => T ((k.factorial:ℝ)⁻¹ • ((A^k) f))) =
      fun k => if k = 0 then T f else 0 := by
    funext k
    cases k with
    | zero => simp
    | succ k => simp only [map_smul, hp, smul_zero, Nat.succ_ne_zero, ↓reduceIte]
  rw [eqs] at hs
  exact hs.unique (hasSum_ite_eq 0 (T f))

theorem gibbsMean_semigroup {n : ℕ} (g : Disorder n) (t : ℝ)
    (f : Observables n) :
    FiniteLaw.mean (mass g 0) (semigroup (coupling g) t f) =
      FiniteLaw.mean (mass g 0) f := by
  simpa only [gibbsMeanCLM_apply, semigroup] using
    functional_exp_invariant (t • generatorCLM (coupling g)) (gibbsMeanCLM g)
    (fun f => by
      rw [smul_apply, map_smul]
      change t • gibbsMeanCLM g (generator (coupling g) f) = 0
      rw [gibbsMean_generator, smul_zero]) f

theorem continuousKernel_stationary {n : ℕ} (g : Disorder n) (t : ℝ) :
    mass g 0 ᵥ* continuousKernel (coupling g) t = mass g 0 := by
  funext y
  have h := gibbsMean_semigroup g t (fun z => if z = y then (1:ℝ) else 0)
  simpa only [FiniteLaw.mean, Matrix.vecMul, continuousKernel, dotProduct,
    mul_ite, mul_one, mul_zero, Fintype.sum_ite_eq'] using h

lemma continuousKernel_stochastic {n : ℕ} (J : Interaction n) {t : ℝ} (ht : 0 ≤ t) :
    continuousKernel J t ∈ Matrix.rowStochastic ℝ (Spin n) := by
  exact Matrix.mem_rowStochastic_iff_sum.mpr
    ⟨continuousKernel_nonneg J t ht, continuousKernel_sum J t⟩

lemma tv_le_continuousDistance {n : ℕ} (g : Disorder n) (t : ℝ) (x : Spin n) :
    totalVariation (continuousKernel (coupling g) t x) (mass g 0) ≤
      continuousDistance g t := by
  unfold continuousDistance
  exact Finset.le_sup' (fun z : Spin n =>
    totalVariation (continuousKernel (coupling g) t z) (mass g 0)) (Finset.mem_univ x)

lemma continuousDistance_le_one {n : ℕ} (g : Disorder n) {t : ℝ} (ht : 0 ≤ t) :
    continuousDistance g t ≤ 1 := by
  apply Finset.sup'_le
  intro x _
  exact totalVariation_le_one _ _ (continuousKernel_nonneg _ t ht x) (mass_nonneg g 0)
    (continuousKernel_sum _ t x) (sum_mass g 0)

lemma continuousDistance_antitone {n : ℕ} (g : Disorder n) {s t : ℝ}
    (_hs : 0 ≤ s) (hst : s ≤ t) : continuousDistance g t ≤ continuousDistance g s := by
  apply Finset.sup'_le
  intro x _
  have htime : t = s + (t-s) := by ring
  have hsum : (∑ y, continuousKernel (coupling g) s x y) = ∑ y, mass g 0 y := by
    rw [continuousKernel_sum, sum_mass]
  calc
    _ = totalVariation (continuousKernel (coupling g) s x ᵥ*
        continuousKernel (coupling g) (t-s))
        (mass g 0 ᵥ* continuousKernel (coupling g) (t-s)) := by
      rw [continuousKernel_stationary]
      conv_lhs => rw [htime, continuousKernel_add, Matrix.mul_apply_eq_vecMul]
    _ ≤ totalVariation (continuousKernel (coupling g) s x) (mass g 0) :=
      totalVariation_contract _ (continuousKernel_stochastic _ (sub_nonneg.mpr hst)) _ _ hsum
    _ ≤ _ := tv_le_continuousDistance g s x

theorem continuousDistance_smoothing {n : ℕ} (g : Disorder n) {t s : ℝ}
    (ht : 0 ≤ t) {ε V W : ℝ} (hε : 0 < ε)
    (hoverlap : continuousDistance g t ≤ 1-ε)
    (htransient : ∀ (x : Spin n) (f : Observables n), (∀ y, |f y| ≤ 1) →
      FiniteLaw.variance (continuousKernel (coupling g) t x)
        (semigroup (coupling g) s f) ≤ V)
    (hequilibrium : ∀ f : Observables n, (∀ y, |f y| ≤ 1) →
      FiniteLaw.variance (mass g 0) (semigroup (coupling g) s f) ≤ W) :
    continuousDistance g (t+s) ≤ (Real.sqrt V+Real.sqrt W)/(2*Real.sqrt ε) := by
  apply Finset.sup'_le
  intro x _
  apply FiniteLaw.totalVariation_le_of_tests
  intro f hf
  have hc := FiniteLaw.common_mass_means (continuousKernel (coupling g) t x) (mass g 0)
    (semigroup (coupling g) s f) (continuousKernel_nonneg _ t ht x) (mass_nonneg g 0)
    (continuousKernel_sum _ t x) (sum_mass g 0) hε
    ((tv_le_continuousDistance g t x).trans hoverlap)
  rw [gibbsMean_semigroup, ← semigroup_eq_kernel, ← mul_apply_eq_comp,
    ← semigroup_add, semigroup_eq_kernel] at hc
  calc
    _ ≤ (Real.sqrt (FiniteLaw.variance (continuousKernel (coupling g) t x)
        (semigroup (coupling g) s f))+
        Real.sqrt (FiniteLaw.variance (mass g 0) (semigroup (coupling g) s f))) /
        Real.sqrt ε := hc
    _ ≤ (Real.sqrt V+Real.sqrt W) / Real.sqrt ε := by
      apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
      exact add_le_add (Real.sqrt_le_sqrt (htransient x f hf))
        (Real.sqrt_le_sqrt (hequilibrium f hf))
    _ = _ := by ring

lemma gradientWeight_le_two {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) :
    gradientWeight J x i ≤ 2 := by
  have hl : -1 < mean J x i := Real.neg_one_lt_tanh _
  have hu : mean J x i < 1 := Real.tanh_lt_one _
  unfold gradientWeight spin
  cases x i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith

lemma weightedGradient_nonneg {n : ℕ} (J : Interaction n) (f : Observables n) (x : Spin n) :
    0 ≤ weightedGradient J f x := by
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (gradientWeight_pos J x i).le (sq_nonneg _))

lemma weightedGradient_le {n : ℕ} (J : Interaction n) (f : Observables n) (x : Spin n) :
    weightedGradient J f x ≤ 2*unweightedGradient f x := by
  rw [unweightedGradient, Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ =>
    mul_le_mul_of_nonneg_right (gradientWeight_le_two J x i) (sq_nonneg _))

lemma halfDiff_abs_le {n : ℕ} (f : Observables n) {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) (x : Spin n) (i : Fin n) : |halfDiff i f x| ≤ B := by
  unfold halfDiff
  rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have h := (abs_sub (f (replace x i true)) (f (replace x i false))).trans
    (add_le_add (hf _) (hf _))
  linarith only [h]

lemma unweightedGradient_le_dim {n : ℕ} (f : Observables n) (hf : ∀ x, |f x| ≤ 1)
    (x : Spin n) : unweightedGradient f x ≤ n := by
  calc
    _ ≤ ∑ _i : Fin n, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact (sq_le_one_iff_abs_le_one _).mpr (halfDiff_abs_le f hf x i)
    _ = _ := by simp

lemma continuous_halfDiff {n : ℕ} (i : Fin n) (F : ℝ → Observables n)
    (hF : Continuous F) (x : Spin n) : Continuous (fun t => halfDiff i (F t) x) := by
  exact (((continuous_apply _).comp hF).sub ((continuous_apply _).comp hF)).div_const 2

lemma continuous_weightedGradient {n : ℕ} (J : Interaction n) (F : ℝ → Observables n)
    (hF : Continuous F) : Continuous (fun t => weightedGradient J (F t)) := by
  apply continuous_pi
  intro x
  exact continuous_finsetSum _ (fun i _ =>
    ((continuous_halfDiff i F hF x).pow 2).const_mul (gradientWeight J x i))

lemma backwardEnergy_continuous {n : ℕ} (J : Interaction n) (f : Observables n)
    (x : Spin n) (T : ℝ) : Continuous (backwardEnergy J f x T) := by
  exact (continuous_apply x).comp ((semigroup_continuous J).clm_apply
    (continuous_weightedGradient J _ (((semigroup_continuous J).comp
      (continuous_const.sub continuous_id)).clm_apply continuous_const)))

lemma backwardEnergy_nonneg {n : ℕ} (J : Interaction n) (f : Observables n)
    (x : Spin n) (T u : ℝ) (hu : 0 ≤ u) : 0 ≤ backwardEnergy J f x T u := by
  exact semigroup_nonneg J u hu _ (weightedGradient_nonneg J _) x

lemma backward_second_moment_hasDerivAt {n : ℕ} (J : Interaction n) (f : Observables n)
    (x : Spin n) (T u : ℝ) :
    HasDerivAt (fun r : ℝ => semigroup J r (fun y => (semigroup J (T-r) f y)^2) x)
      (2*backwardEnergy J f x T u) u := by
  let F : ℝ → Observables n := fun r => semigroup J (T-r) f
  have hF : HasDerivAt F (-generator J (F u)) u := by
    simpa only [Function.comp_def, sub_zero, zero_sub, neg_smul, one_smul] using
      (semigroup_apply_hasDerivAt' J f (T-u)).scomp u
        ((hasDerivAt_const u T).sub (hasDerivAt_id u))
  have hsq : HasDerivAt (fun r : ℝ => (fun y => (F r y)^2))
      (fun y => -2*F u y*generator J (F u) y) u := by
    apply hasDerivAt_pi.mpr
    intro y
    convert (hasDerivAt_pi.mp hF y).fun_pow 2 using 1
    all_goals try with_reducible_and_instances rfl
    simp only [Pi.neg_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    ring
  have H := (semigroup_hasDerivAt J u).clm_apply hsq
  have heq : (semigroup J u*generatorCLM J) (fun y => F u y^2) +
      semigroup J u (fun y => -2*F u y*generator J (F u) y) =
      (2:ℝ) • semigroup J u (weightedGradient J (F u)) := by
    rw [mul_apply_eq_comp, ← map_add, ← map_smul]
    congr 1
    funext y
    change generator J (fun y => F u y^2) y + (-2*F u y*generator J (F u) y) =
      2*weightedGradient J (F u) y
    have h := variance_density J (F u) y
    linarith only [h]
  rw [heq] at H
  exact hasDerivAt_pi.mp H x

theorem backward_variance_budget {n : ℕ} (J : Interaction n) (f : Observables n)
    (x : Spin n) (T r : ℝ) :
    FiniteLaw.variance (continuousKernel J r x) (semigroup J (T-r) f) =
      2*∫ u in (0:ℝ)..r, backwardEnergy J f x T u := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => backward_second_moment_hasDerivAt J f x T u)
    ((backwardEnergy_continuous J f x T).const_mul 2 |>.intervalIntegrable 0 r)
  rw [intervalIntegral.integral_const_mul] at hi
  rw [FiniteLaw.variance_eq _ _ (continuousKernel_sum J r x),
    ← semigroup_eq_kernel, ← semigroup_eq_kernel,
    ← mul_apply_eq_comp, ← semigroup_add]
  have heq : r+(T-r) = T := by ring
  rw [heq]
  simpa only [semigroup_zero, one_apply_eq_self, sub_zero] using hi.symm

theorem backward_energy_budget {n : ℕ} (J : Interaction n) (f : Observables n)
    (hf : ∀ y, |f y| ≤ 1) (x : Spin n) {T : ℝ} (hT : 0 ≤ T) :
    (∫ u in (0:ℝ)..T, backwardEnergy J f x T u) ≤ 1/2 := by
  have hi := backward_variance_budget J f x T T
  simp only [sub_self, semigroup_zero, one_apply_eq_self] at hi
  rw [FiniteLaw.variance_eq _ _ (continuousKernel_sum J T x), ← semigroup_eq_kernel,
    ← semigroup_eq_kernel] at hi
  have hsquares : ∀ y, f y^2 ≤ (1:ℝ) := fun y => (sq_le_one_iff_abs_le_one _).mpr (hf y)
  have hm := semigroup_mono J hT (fun y => f y^2) (fun _ => 1) hsquares x
  rw [semigroup_const] at hm
  linarith [sq_nonneg (semigroup J T f x)]

end SKRatio.Calculus

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_Energy
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
attribute [-simp] _root_.OAI.SKRatio.Calculus.continuousDistance_zero _root_.OAI.SKRatio.Calculus.continuousKernel_zero _root_.OAI.SKRatio.Calculus.field_reversal _root_.OAI.SKRatio.Calculus.gibbsEuclideanEquiv_apply _root_.OAI.SKRatio.Calculus.lift_scalarEigenfunction _root_.OAI.SKRatio.Calculus.mass_reversal _root_.OAI.SKRatio.Calculus.reversal_reversal _root_.OAI.SKRatio.Calculus.spin_reversal _root_.OAI.SKRatio.Calculus.stationaryPairingCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap MeasureTheory Filter
namespace SKRatio.Calculus

lemma energy_early_late_averaging (G : ℝ → ℝ) (hcontinuous : Continuous G)
    {t s a R : ℝ} (ht : 0 ≤ t) (hs : 0 < s) (ha : 0 ≤ a)
    (hnonneg : ∀ u ∈ Set.Icc (0:ℝ) (t+s), 0 ≤ G u)
    (hbudget : (∫ u in (0:ℝ)..(t+s), G u) ≤ 1/2)
    (hcompare : ∀ u ∈ Set.Icc (0:ℝ) t,
      ∀ z ∈ Set.Icc (t+s/2) (t+s), G u ≤ a*G z+R) :
    (∫ u in (0:ℝ)..t, G u) ≤ t*(a/s+R) := by
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hcontinuous.intervalIntegrable 0 (t+s/2))
    (hcontinuous.intervalIntegrable (t+s/2) (t+s))
  have hfirst : 0 ≤ ∫ u in (0:ℝ)..(t+s/2), G u := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro u hu
    exact hnonneg u ⟨hu.1, by linarith [hu.2]⟩
  have hlate : (∫ u in (t+s/2)..(t+s), G u) ≤ 1/2 := by
    linarith only [hsplit, hfirst, hbudget]
  have hearly (u : ℝ) (hu : u ∈ Set.Icc (0:ℝ) t) : G u ≤ a/s+R := by
    have hi := intervalIntegral.integral_mono_on (μ := volume) (by linarith : t+s/2 ≤ t+s)
      (continuous_const.intervalIntegrable (t+s/2) (t+s))
      ((hcontinuous.const_mul a |>.add_const R).intervalIntegrable (t+s/2) (t+s))
      (hcompare u hu)
    rw [intervalIntegral.integral_const,
      intervalIntegral.integral_add ((hcontinuous.const_mul a).intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hi
    simp only [smul_eq_mul] at hi
    have hlate' := mul_le_mul_of_nonneg_left hlate ha
    have heq : s*(a/s)=a := by field_simp
    nlinarith only [hi, hlate', heq, hs]
  calc
    _ ≤ ∫ _u in (0:ℝ)..t, (a/s+R) :=
      intervalIntegral.integral_mono_on ht (hcontinuous.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _) hearly
    _ = _ := by rw [intervalIntegral.integral_const]; simp

theorem transient_variance_of_energy_comparison {n : ℕ} (J : Interaction n)
    (f : Observables n) (hf : ∀ y, |f y| ≤ 1) (x : Spin n)
    {t s a R : ℝ} (ht : 0 ≤ t) (hs : 0 < s) (ha : 0 ≤ a)
    (hcompare : ∀ u ∈ Set.Icc (0:ℝ) t,
      ∀ z ∈ Set.Icc (t+s/2) (t+s),
      backwardEnergy J f x (t+s) u ≤ a*backwardEnergy J f x (t+s) z+R) :
    FiniteLaw.variance (continuousKernel J t x) (semigroup J s f) ≤
      2*t*(a/s+R) := by
  have H := energy_early_late_averaging (backwardEnergy J f x (t+s))
    (backwardEnergy_continuous J f x (t+s)) ht hs ha
    (fun u hu => backwardEnergy_nonneg J f x (t+s) u hu.1)
    (backward_energy_budget J f hf x (by linarith)) hcompare
  have hv := backward_variance_budget J f x (t+s) t
  rw [show t+s-t = s by ring] at hv
  rw [hv]
  linarith only [H]

lemma stationaryEnergy_eq {n : ℕ} (g : Disorder n) (f : Observables n) :
    stationaryEnergy g f =
      -FiniteLaw.mean (mass g 0) (fun x => f x*generator (coupling g) f x) := by
  have hg : generator (coupling g) (fun x => f x^2) =
      (2:ℝ) • ((fun x => f x*generator (coupling g) f x) +
        weightedGradient (coupling g) f) := by
    funext x
    change generator (coupling g) (fun y => f y^2) x =
      2*(f x*generator (coupling g) f x + weightedGradient (coupling g) f x)
    have h := variance_density (coupling g) f x
    linarith only [h]
  have h := congrArg (gibbsMeanCLM g) hg
  rw [gibbsMean_generator, map_smul, map_add] at h
  simp only [gibbsMeanCLM_apply, smul_eq_mul] at h
  unfold stationaryEnergy
  linarith only [h]

lemma equilibrium_variance_hasDerivAt {n : ℕ} (g : Disorder n) (f : Observables n)
    (t : ℝ) :
    HasDerivAt (fun r => FiniteLaw.variance (mass g 0) (semigroup (coupling g) r f))
      (-2*stationaryEnergy g (semigroup (coupling g) t f)) t := by
  have hsq : HasDerivAt (fun r : ℝ => fun x : Spin n => (semigroup (coupling g) r f x)^2)
      (fun x => 2*semigroup (coupling g) t f x*
        generator (coupling g) (semigroup (coupling g) t f) x) t := by
    apply hasDerivAt_pi.mpr
    intro x
    have h := (hasDerivAt_pi.mp (semigroup_apply_hasDerivAt' (coupling g) f t) x).fun_pow 2
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  have hm := (gibbsMeanCLM g).hasFDerivAt.comp_hasDerivAt t hsq
  have hm' := hm.sub_const ((FiniteLaw.mean (mass g 0) f)^2)
  have heq : (fun r => FiniteLaw.variance (mass g 0) (semigroup (coupling g) r f)) =
      (fun r => gibbsMeanCLM g (fun x => (semigroup (coupling g) r f x)^2) -
        (FiniteLaw.mean (mass g 0) f)^2) := by
    funext r
    rw [FiniteLaw.variance_eq _ _ (sum_mass g 0), gibbsMean_semigroup, gibbsMeanCLM_apply]
  rw [heq]
  apply hm'.congr_deriv
  rw [stationaryEnergy_eq]
  simp only [gibbsMeanCLM_apply, FiniteLaw.mean, mul_neg, neg_mul, neg_neg, Finset.mul_sum, Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem equilibrium_variance_decay {n : ℕ} (g : Disorder n) {γ : ℝ}
    (hgap : ∀ f : Observables n,
      γ*FiniteLaw.variance (mass g 0) f ≤ stationaryEnergy g f)
    (f : Observables n) {s : ℝ} (hs : 0 ≤ s) :
    FiniteLaw.variance (mass g 0) (semigroup (coupling g) s f) ≤
      Real.exp (-2*γ*s)*FiniteLaw.variance (mass g 0) f := by
  let V (r : ℝ) := FiniteLaw.variance (mass g 0) (semigroup (coupling g) r f)
  let E (r : ℝ) := stationaryEnergy g (semigroup (coupling g) r f)
  let H (r : ℝ) := Real.exp (2*γ*r)*V r
  have hderiv (r : ℝ) : HasDerivAt H (Real.exp (2*γ*r)*(2*γ*V r-2*E r)) r := by
    have h := (((hasDerivAt_id r).const_mul (2*γ)).exp).mul
      (equilibrium_variance_hasDerivAt g f r)
    convert h using 1 <;> first | rfl | (dsimp [V, E]; ring)
  have hanti : Antitone H := antitone_of_deriv_nonpos
    (fun r => (hderiv r).differentiableAt) (fun r => by
      rw [(hderiv r).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _) (by
        have h := hgap (semigroup (coupling g) r f)
        change γ*V r ≤ E r at h
        linarith only [h]))
  have h := hanti hs
  have hzero : H 0 = FiniteLaw.variance (mass g 0) f := by
    simp [H, V]
  rw [hzero] at h
  have hscaled := mul_le_mul_of_nonneg_left h (Real.exp_nonneg (-2*γ*s))
  calc
    V s = Real.exp (-2*γ*s)*H s := by
      dsimp [H]
      rw [← mul_assoc, ← Real.exp_add, show -2*γ*s+2*γ*s=0 by ring, Real.exp_zero, one_mul]
    _ ≤ _ := hscaled

lemma equilibrium_variance_le_one {n : ℕ} (g : Disorder n) (f : Observables n)
    (hf : ∀ x, |f x| ≤ 1) : FiniteLaw.variance (mass g 0) f ≤ 1 := by
  have hle : FiniteLaw.mean (mass g 0) (fun x => f x^2) ≤ 1 := by
    calc
      _ ≤ ∑ x : Spin n, mass g 0 x*1 :=
        Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left
          ((sq_le_one_iff_abs_le_one _).mpr (hf x)) (mass_nonneg g 0 x))
      _ = _ := by simp [sum_mass]
  rw [FiniteLaw.variance_eq _ _ (sum_mass g 0)]
  linarith only [hle, sq_nonneg (FiniteLaw.mean (mass g 0) f)]

theorem equilibrium_smoothing {n : ℕ} (g : Disorder n) {γ : ℝ}
    (hgap : ∀ f : Observables n,
      γ*FiniteLaw.variance (mass g 0) f ≤ stationaryEnergy g f)
    (f : Observables n) (hf : ∀ x, |f x| ≤ 1) {s : ℝ} (hs : 0 ≤ s) :
    FiniteLaw.variance (mass g 0) (semigroup (coupling g) s f) ≤ Real.exp (-2*γ*s) := by
  exact (equilibrium_variance_decay g hgap f hs).trans
    ((mul_le_mul_of_nonneg_left (equilibrium_variance_le_one g f hf)
      (Real.exp_nonneg _)).trans_eq (mul_one _))

theorem smoothing_of_energy_comparison {n : ℕ} (g : Disorder n)
    {t s a R γ ε : ℝ} (ht : 0 ≤ t) (hs : 0 < s) (ha : 0 ≤ a) (hε : 0 < ε)
    (hoverlap : continuousDistance g t ≤ 1-ε)
    (hgap : ∀ f : Observables n,
      γ*FiniteLaw.variance (mass g 0) f ≤ stationaryEnergy g f)
    (hcompare : ∀ (f : Observables n), (∀ y, |f y| ≤ 1) →
      ∀ (x : Spin n), ∀ u ∈ Set.Icc (0:ℝ) t,
      ∀ z ∈ Set.Icc (t+s/2) (t+s),
      backwardEnergy (coupling g) f x (t+s) u ≤
        a*backwardEnergy (coupling g) f x (t+s) z+R) :
    continuousDistance g (t+s) ≤
      (Real.sqrt (2*t*(a/s+R))+Real.exp (-γ*s))/(2*Real.sqrt ε) := by
  have h := continuousDistance_smoothing g ht hε hoverlap
    (fun x f hf => transient_variance_of_energy_comparison (coupling g)
      f hf x ht hs ha (hcompare f hf x))
    (fun f hf => equilibrium_smoothing g hgap f hf hs.le)
  have heq : Real.sqrt (Real.exp (-2*γ*s)) = Real.exp (-γ*s) := by
    rw [show -2*γ*s = (2:ℕ)*(-γ*s) by push_cast; ring,
      Real.exp_nat_mul, Real.sqrt_sq (Real.exp_nonneg _)]
  rwa [heq] at h

end SKRatio.Calculus

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Dynamics_Concentration
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology _root_.OAI.SKRatioGaussian.instNonemptyUnitBall
attribute [-simp] _root_.OAI.SKRatio.Calculus.continuousKernel_zero _root_.OAI.SKRatio.Calculus.field_reversal _root_.OAI.SKRatio.Calculus.gibbsEuclideanEquiv_apply _root_.OAI.SKRatio.Calculus.gibbsMeanCLM_apply _root_.OAI.SKRatio.Calculus.lift_scalarEigenfunction _root_.OAI.SKRatio.Calculus.mass_reversal _root_.OAI.SKRatio.Calculus.reversal_reversal _root_.OAI.SKRatio.Calculus.spin_reversal _root_.OAI.SKRatio.Calculus.stationaryPairingCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap MeasureTheory Filter
namespace SKRatio.Calculus

lemma flip_sub {n : ℕ} (f : Observables n) (x : Spin n) (i : Fin n) :
    f (flip i x)-f x = -2*spin x i*halfDiff i f x := by
  have hx := replace_self x i
  cases hi : x i <;> simp only [hi] at hx
  · simp only [spin, hi, Bool.false_eq_true, ↓reduceIte, flip, Bool.not_false, halfDiff]
    rw [hx]
    simp only [replace]
    ring
  · simp only [spin, hi, ↓reduceIte, flip, Bool.not_true, halfDiff]
    rw [hx]
    simp only [replace]
    ring

lemma backward_flow_hasDerivAt {n : ℕ} (J : Interaction n) (f : Observables n) (d s : ℝ) :
    HasDerivAt (fun r : ℝ => semigroup J (d - r) f)
      (fun x => -generator J (semigroup J (d - s) f) x) s := by
  have h := (semigroup_apply_hasDerivAt' J f (d - s)).scomp s
    ((hasDerivAt_id s).const_sub d)
  simpa only [id_eq, neg_smul, one_smul, Pi.neg_def, Function.comp_def] using h

lemma backward_square_hasDerivAt {n : ℕ} (J : Interaction n) (f : Observables n) (d s : ℝ) :
    HasDerivAt (fun r : ℝ => fun x : Spin n => (semigroup J (d - r) f x) ^ 2)
      (fun x => -2 * semigroup J (d - s) f x * generator J (semigroup J (d - s) f) x) s := by
  apply hasDerivAt_pi.mpr
  intro x
  have h := (hasDerivAt_pi.mp (backward_flow_hasDerivAt J f d s) x).pow 2
  have he : (2 : ℝ) * semigroup J (d - s) f x *
      -generator J (semigroup J (d - s) f) x =
      -2 * semigroup J (d - s) f x * generator J (semigroup J (d - s) f) x := by ring
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  try rfl
  simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using he.symm

lemma interpolated_square_hasDerivAt {n : ℕ} (J : Interaction n) (f : Observables n) (d s : ℝ) :
    HasDerivAt (fun r : ℝ => semigroup J r
      (fun x => (semigroup J (d - r) f x) ^ 2))
      (semigroup J s (jumpEnergy J (semigroup J (d - s) f))) s := by
  have h := (semigroup_hasDerivAt J s).clm_apply (backward_square_hasDerivAt J f d s)
  apply h.congr_deriv
  simp only [mul_apply_eq_comp]
  change semigroup J s (generator J (fun x => semigroup J (d - s) f x ^ 2)) +
    semigroup J s (fun x => -2 * semigroup J (d - s) f x *
      generator J (semigroup J (d - s) f) x) = _
  rw [← map_add]
  congr 1
  funext x
  rw [generator_square]
  simp only [Pi.add_apply]
  ring

lemma jumpEnergy_continuous {n : ℕ} (J : Interaction n) :
    Continuous (jumpEnergy J) := by
  unfold jumpEnergy halfDiff
  fun_prop

lemma interpolated_energy_continuous {n : ℕ} (J : Interaction n) (f : Observables n)
    (d : ℝ) (x : Spin n) :
    Continuous (fun s : ℝ => semigroup J s (jumpEnergy J (semigroup J (d - s) f)) x) := by
  have hc : Continuous (fun s : ℝ => semigroup J (d - s) f) :=
    ((semigroup_continuous J).comp (continuous_const.sub continuous_id)).clm_apply continuous_const
  exact continuous_apply x |>.comp ((semigroup_continuous J).clm_apply
    ((jumpEnergy_continuous J).comp hc))

lemma semigroup_variance_integral {n : ℕ} (J : Interaction n) (f : Observables n)
    (d : ℝ) (x : Spin n) :
    semigroup J d (fun y => f y ^ 2) x - (semigroup J d f x) ^ 2 =
      ∫ s in (0 : ℝ)..d, semigroup J s (jumpEnergy J (semigroup J (d - s) f)) x := by
  have hd (s : ℝ) := hasDerivAt_pi.mp (interpolated_square_hasDerivAt J f d s) x
  have hi := (interpolated_energy_continuous J f d x).intervalIntegrable
    (μ := MeasureTheory.volume) 0 d
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) hi
  simpa only [sub_self, sub_zero, semigroup_zero, one_apply_eq_self] using he.symm

lemma jumpWeight_bounds {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) :
    0 ≤ 1 - mean J x i * spin x i ∧ 1 - mean J x i * spin x i ≤ 2 := by
  have hl := Real.neg_one_lt_tanh (field J x i)
  have hu := Real.tanh_lt_one (field J x i)
  cases hs : x i <;> simp only [spin, hs, Bool.false_eq_true, ↓reduceIte, mul_one,
    mul_neg, sub_neg_eq_add, mean] <;> constructor <;> linarith

lemma jumpEnergy_le_gradient {n : ℕ} (J : Interaction n) (f : Observables n) (x : Spin n) :
    jumpEnergy J f x ≤ 4 * ∑ i, (halfDiff i f x) ^ 2 := by
  unfold jumpEnergy
  calc
    _ ≤ 2 * ∑ i, 2 * (halfDiff i f x) ^ 2 := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum _) (by norm_num)
      intro i _
      exact mul_le_mul_of_nonneg_right (jumpWeight_bounds J x i).2 (sq_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]; ring

lemma semigroup_le_const {n : ℕ} (J : Interaction n) (t : ℝ) (ht : 0 ≤ t)
    {f : Observables n} {C : ℝ} (hf : ∀ x, f x ≤ C) (x : Spin n) :
    semigroup J t f x ≤ C := by
  simpa only [semigroup_const] using semigroup_mono J ht _ _ hf x

theorem semigroup_variance_le {n : ℕ} (J : Interaction n) (f : Observables n)
    (d : ℝ) (hd : 0 ≤ d) (b : ℝ → ℝ)
    (hb : IntervalIntegrable b MeasureTheory.volume 0 d)
    (hbound : ∀ r ∈ Set.Icc (0 : ℝ) d, ∀ x, ∑ i, (halfDiff i (semigroup J r f) x) ^ 2 ≤ b r)
    (x : Spin n) :
    semigroup J d (fun y => f y ^ 2) x - (semigroup J d f x) ^ 2 ≤
      4 * ∫ r in (0 : ℝ)..d, b r := by
  rw [semigroup_variance_integral]
  have hbr : IntervalIntegrable (fun s => b (d - s)) MeasureTheory.volume 0 d := by
    simpa only [sub_self, sub_zero] using (hb.comp_sub_left d).symm
  calc
    _ ≤ ∫ s in (0 : ℝ)..d, 4 * b (d - s) := by
      apply intervalIntegral.integral_mono_on hd
        ((interpolated_energy_continuous J f d x).intervalIntegrable 0 d)
        (hbr.const_mul 4)
      intro s hs
      apply semigroup_le_const J s hs.1
      intro y
      exact (jumpEnergy_le_gradient J (semigroup J (d - s) f) y).trans
        (mul_le_mul_of_nonneg_left (hbound (d - s) ⟨sub_nonneg.mpr hs.2, by linarith [hs.1]⟩ y)
          (by norm_num))
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_left]
      simp only [sub_self, sub_zero]

lemma real_exp_remainder_le (z : ℝ) :
    Real.exp z - 1 - z ≤ z ^ 2 * Real.exp |z| / 2 := by
  by_cases hz : z = 0
  · simp [hz]
  have hn : (0 : ℝ) ≠ z := Ne.symm hz
  obtain ⟨u, hu, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 1) (f := Real.exp) hn Real.contDiff_exp.contDiffOn
  have hd : derivWithin Real.exp (Set.uIcc 0 z) 0 = 1 := by
    simpa using (Real.hasDerivAt_exp 0).hasDerivWithinAt.derivWithin
      ((uniqueDiffOn_uIcc hn) 0 (Set.left_mem_uIcc))
  have hi : iteratedDeriv 2 Real.exp = Real.exp := by
    simpa using iteratedDeriv_exp_const_mul 2 (1 : ℝ)
  simp [taylorWithinEval_succ, iteratedDerivWithin_one, hd, hi] at he
  have hu' : u ≤ |z| := by
    calc
      u ≤ max 0 z := le_of_lt hu.2
      _ ≤ |z| := max_le (abs_nonneg _) (le_abs_self _)
  calc
    Real.exp z - 1 - z = Real.exp u * z ^ 2 / 2 := by linarith [he]
    _ ≤ z ^ 2 * Real.exp |z| / 2 := by
      have h := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hu') (sq_nonneg z)
      nlinarith

lemma expDrift_eq_sum {n : ℕ} (J : Interaction n) (θ : ℝ) (f : Observables n) (x : Spin n) :
    expDrift J θ f x = Real.exp (θ * f x) * ∑ i, flipRate J x i *
      (Real.exp (θ * (f (flip i x) - f x)) - 1 - θ * (f (flip i x) - f x)) := by
  have he (i : Fin n) : Real.exp (θ * f (flip i x)) =
      Real.exp (θ * f x) * Real.exp (θ * (f (flip i x) - f x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [expDrift, generator_flip, he, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma flipRate_nonneg {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) :
    0 ≤ flipRate J x i := by
  unfold flipRate
  exact div_nonneg (by simpa only [mul_comm] using (jumpWeight_bounds J x i).1) (by norm_num)

lemma jumpEnergy_eq_jump_square {n : ℕ} (J : Interaction n) (f : Observables n) (x : Spin n) :
    jumpEnergy J f x = ∑ i, flipRate J x i * (f (flip i x) - f x) ^ 2 := by
  simp only [jumpEnergy, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [flip_sub]
  simp only [mul_pow, spin_sq, mul_one, flipRate]
  ring

lemma abs_flip_sub_le {n : ℕ} (f : Observables n) (x : Spin n) (B : ℝ)
    (hB : ∑ j, (halfDiff j f x) ^ 2 ≤ B) (i : Fin n) :
    |f (flip i x) - f x| ≤ 2 * Real.sqrt B := by
  have hi : (halfDiff i f x) ^ 2 ≤ B :=
    (Finset.single_le_sum (fun j _ => sq_nonneg (halfDiff j f x)) (Finset.mem_univ i)).trans hB
  have hs : |spin x i| = 1 := by cases hx : x i <;> simp [spin, hx]
  rw [flip_sub, abs_mul, abs_mul, hs]
  norm_num
  exact Real.abs_le_sqrt hi

lemma expDrift_le {n : ℕ} (J : Interaction n) (θ : ℝ) (f : Observables n) (x : Spin n)
    (B b : ℝ) (hB : ∑ i, (halfDiff i f x) ^ 2 ≤ B)
    (hb : ∑ i, (halfDiff i f x) ^ 2 ≤ b) :
    expDrift J θ f x ≤ (2 * θ ^ 2 * Real.exp (2 * |θ| * Real.sqrt B) * b) *
      Real.exp (θ * f x) := by
  let R := Real.exp (2 * |θ| * Real.sqrt B)
  have hR : 0 ≤ θ ^ 2 * R / 2 := by positivity
  have hrem (i : Fin n) :
      Real.exp (θ * (f (flip i x) - f x)) - 1 - θ * (f (flip i x) - f x) ≤
        θ ^ 2 * R / 2 * (f (flip i x) - f x) ^ 2 := by
    have ha : |θ * (f (flip i x) - f x)| ≤ 2 * |θ| * Real.sqrt B := by
      rw [abs_mul]
      calc
        _ ≤ |θ| * (2 * Real.sqrt B) :=
          mul_le_mul_of_nonneg_left (abs_flip_sub_le f x B hB i) (abs_nonneg θ)
        _ = _ := by ring
    calc
      _ ≤ (θ * (f (flip i x) - f x)) ^ 2 *
          Real.exp |θ * (f (flip i x) - f x)| / 2 := real_exp_remainder_le _
      _ ≤ (θ * (f (flip i x) - f x)) ^ 2 * R / 2 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ha) (sq_nonneg _)
      _ = _ := by ring
  rw [expDrift_eq_sum]
  calc
    _ ≤ Real.exp (θ * f x) * ∑ i, flipRate J x i *
        (θ ^ 2 * R / 2 * (f (flip i x) - f x) ^ 2) := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum _) (Real.exp_pos _).le
      intro i _
      exact mul_le_mul_of_nonneg_left (hrem i) (flipRate_nonneg J x i)
    _ = Real.exp (θ * f x) * (θ ^ 2 * R / 2) * jumpEnergy J f x := by
      rw [jumpEnergy_eq_jump_square]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ Real.exp (θ * f x) * (θ ^ 2 * R / 2) * (4 * b) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Real.exp_pos _).le hR)
      exact (jumpEnergy_le_gradient J f x).trans (mul_le_mul_of_nonneg_left hb (by norm_num))
    _ = _ := by dsimp [R]; ring

lemma backward_exp_hasDerivAt {n : ℕ} (J : Interaction n) (f : Observables n)
    (θ d s : ℝ) :
    HasDerivAt (fun r : ℝ => fun x : Spin n => Real.exp (θ * semigroup J (d - r) f x))
      (fun x => -θ * Real.exp (θ * semigroup J (d - s) f x) *
        generator J (semigroup J (d - s) f) x) s := by
  apply hasDerivAt_pi.mpr
  intro x
  have h := ((hasDerivAt_pi.mp (backward_flow_hasDerivAt J f d s) x).const_mul θ).exp
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  try rfl
  ring

lemma interpolated_exp_hasDerivAt {n : ℕ} (J : Interaction n) (f : Observables n)
    (θ d s : ℝ) :
    HasDerivAt (fun r : ℝ => semigroup J r
      (fun x => Real.exp (θ * semigroup J (d - r) f x)))
      (semigroup J s (expDrift J θ (semigroup J (d - s) f))) s := by
  have h := (semigroup_hasDerivAt J s).clm_apply (backward_exp_hasDerivAt J f θ d s)
  apply h.congr_deriv
  simp only [mul_apply_eq_comp]
  change semigroup J s (generator J (fun x => Real.exp (θ * semigroup J (d - s) f x))) +
    semigroup J s (fun x => -θ * Real.exp (θ * semigroup J (d - s) f x) *
      generator J (semigroup J (d - s) f) x) = _
  rw [← map_add]
  congr 1
  funext x
  simp only [Pi.add_apply, expDrift]
  ring

lemma semigroup_pos {n : ℕ} (J : Interaction n) (t : ℝ) (ht : 0 ≤ t)
    {f : Observables n} (hf : ∀ x, 0 < f x) (x : Spin n) : 0 < semigroup J t f x := by
  obtain ⟨y, _, hy⟩ := Finset.exists_min_image (Finset.univ : Finset (Spin n)) f
    Finset.univ_nonempty
  have h := semigroup_mono J ht _ _ (fun z => hy z (Finset.mem_univ z)) x
  exact (hf y).trans_le (by simpa only [semigroup_const] using h)

lemma expDrift_continuous {n : ℕ} (J : Interaction n) (θ : ℝ) :
    Continuous (expDrift J θ) := by
  unfold expDrift generator halfDiff
  fun_prop

lemma interpolated_exp_continuous {n : ℕ} (J : Interaction n) (f : Observables n)
    (θ d : ℝ) (x : Spin n) :
    Continuous (fun s : ℝ => semigroup J s
      (fun y => Real.exp (θ * semigroup J (d - s) f y)) x) := by
  exact continuous_apply x |>.comp
    ((show Differentiable ℝ (fun s : ℝ => semigroup J s
      (fun y => Real.exp (θ * semigroup J (d - s) f y))) from
      fun s => (interpolated_exp_hasDerivAt J f θ d s).differentiableAt).continuous)

lemma interpolated_expDrift_continuous {n : ℕ} (J : Interaction n) (f : Observables n)
    (θ d : ℝ) (x : Spin n) :
    Continuous (fun s : ℝ => semigroup J s (expDrift J θ (semigroup J (d - s) f)) x) := by
  have hc : Continuous (fun s : ℝ => semigroup J (d - s) f) :=
    ((semigroup_continuous J).comp (continuous_const.sub continuous_id)).clm_apply continuous_const
  exact continuous_apply x |>.comp ((semigroup_continuous J).clm_apply
    ((expDrift_continuous J θ).comp hc))

theorem semigroup_jump_mgf {n : ℕ} (J : Interaction n) (f : Observables n)
    (d : ℝ) (hd : 0 ≤ d) (b : ℝ → ℝ) (B θ : ℝ)
    (hb : IntervalIntegrable b MeasureTheory.volume 0 d)
    (hB : ∀ r ∈ Set.Icc (0 : ℝ) d, b r ≤ B)
    (hbound : ∀ r ∈ Set.Icc (0 : ℝ) d, ∀ x, ∑ i, (halfDiff i (semigroup J r f) x) ^ 2 ≤ b r)
    (x : Spin n) :
    semigroup J d (fun y => Real.exp (θ * (f y - semigroup J d f x))) x ≤
      Real.exp (2 * θ ^ 2 * Real.exp (2 * |θ| * Real.sqrt B) * ∫ r in (0 : ℝ)..d, b r) := by
  let F (s : ℝ) := semigroup J s (fun y => Real.exp (θ * semigroup J (d - s) f y)) x
  let F' (s : ℝ) := semigroup J s (expDrift J θ (semigroup J (d - s) f)) x
  let K := 2 * θ ^ 2 * Real.exp (2 * |θ| * Real.sqrt B)
  have hFpos (s : ℝ) (hs : 0 ≤ s) : 0 < F s :=
    semigroup_pos J s hs (fun y => Real.exp_pos _) x
  have hFderiv (s : ℝ) : HasDerivAt F (F' s) s :=
    hasDerivAt_pi.mp (interpolated_exp_hasDerivAt J f θ d s) x
  have hlog (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) d) :
      HasDerivAt (fun r => Real.log (F r)) (F' s / F s) s :=
    (hFderiv s).log (hFpos s hs.1).ne'
  have hcont : ContinuousOn (fun s => F' s / F s) (Set.uIcc (0 : ℝ) d) := by
    apply (interpolated_expDrift_continuous J f θ d x).continuousOn.div
      (interpolated_exp_continuous J f θ d x).continuousOn
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) d := by simpa only [Set.uIcc_of_le hd] using hs
    exact (hFpos s hs'.1).ne'
  have hI : Real.log (F d) - Real.log (F 0) =
      ∫ s in (0 : ℝ)..d, F' s / F s := by
    symm
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hcont.intervalIntegrable
    intro s hs
    exact hlog s (by simpa only [Set.uIcc_of_le hd] using hs)
  have hbr : IntervalIntegrable (fun s => b (d - s)) MeasureTheory.volume 0 d := by
    simpa only [sub_self, sub_zero] using (hb.comp_sub_left d).symm
  have hle : Real.log (F d) - Real.log (F 0) ≤ K * ∫ r in (0 : ℝ)..d, b r := by
    rw [hI]
    calc
      _ ≤ ∫ s in (0 : ℝ)..d, K * b (d - s) := by
        apply intervalIntegral.integral_mono_on hd hcont.intervalIntegrable (hbr.const_mul K)
        intro s hs
        apply (div_le_iff₀ (hFpos s hs.1)).mpr
        have hr : d - s ∈ Set.Icc (0 : ℝ) d := ⟨sub_nonneg.mpr hs.2, by linarith [hs.1]⟩
        have hp := semigroup_mono J hs.1 _ _
          (fun y => expDrift_le J θ (semigroup J (d - s) f) y B (b (d - s))
            ((hbound (d - s) hr y).trans (hB (d - s) hr)) (hbound (d - s) hr y)) x
        change F' s ≤ semigroup J s ((K * b (d - s)) •
          (fun y => Real.exp (θ * semigroup J (d - s) f y))) x at hp
        simpa only [map_smul, Pi.smul_apply, smul_eq_mul] using hp
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_left]
        simp only [sub_self, sub_zero]
  have hF0 : F 0 = Real.exp (θ * semigroup J d f x) := by
    dsimp [F]
    rw [sub_zero, semigroup_zero, one_apply_eq_self]
  have hFd : F d = semigroup J d (fun y => Real.exp (θ * f y)) x := by
    simp only [F, sub_self, semigroup_zero, one_apply_eq_self]
  rw [hF0, Real.log_exp] at hle
  have hle' := (Real.log_le_iff_le_exp (hFpos d hd)).mp (sub_le_iff_le_add.mp hle)
  have hfactor : (fun y => Real.exp (θ * (f y - semigroup J d f x))) =
      Real.exp (-(θ * semigroup J d f x)) • (fun y => Real.exp (θ * f y)) := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, mul_sub, Real.exp_sub, Real.exp_neg]
    ring
  rw [hfactor, map_smul, Pi.smul_apply, smul_eq_mul]
  calc
    _ ≤ Real.exp (-(θ * semigroup J d f x)) *
        Real.exp (K * (∫ r in (0 : ℝ)..d, b r) + θ * semigroup J d f x) :=
      mul_le_mul_of_nonneg_left (by rwa [hFd] at hle') (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [K]; ring

end SKRatio.Calculus

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Dynamics_Propagation
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
attribute [-simp] _root_.OAI.SKRatio.Calculus.continuousKernel_zero _root_.OAI.SKRatio.Calculus.field_reversal _root_.OAI.SKRatio.Calculus.gibbsEuclideanEquiv_apply _root_.OAI.SKRatio.Calculus.lift_scalarEigenfunction _root_.OAI.SKRatio.Calculus.mass_reversal _root_.OAI.SKRatio.Calculus.reversal_reversal _root_.OAI.SKRatio.Calculus.spin_reversal _root_.OAI.SKRatio.Calculus.stationaryPairingCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap MeasureTheory Filter
namespace SKRatio.Calculus
attribute [local instance] Classical.propDecidable

lemma backward_observable_hasDerivAt {n : ℕ} (J : Interaction n)
    (F F' : ℝ → Observables n) (hF : ∀ r, HasDerivAt F (F' r) r)
    (d a u : ℝ) (x : Spin n) :
    HasDerivAt (fun v : ℝ => Real.exp (a*v)*semigroup J v (F (d-v)) x)
      (Real.exp (a*u)*semigroup J u
        (fun y => a*F (d-u) y + generator J (F (d-u)) y - F' (d-u) y) x) u := by
  have hb : HasDerivAt (fun v : ℝ => F (d-v)) (-F' (d-u)) u := by
    simpa only [Function.comp_def, sub_zero, zero_sub, neg_smul, one_smul] using
      (hF (d-u)).scomp u ((hasDerivAt_const u d).sub (hasDerivAt_id u))
  have h := (((hasDerivAt_id u).const_mul a).exp).mul
    (hasDerivAt_pi.mp ((semigroup_hasDerivAt J u).clm_apply hb) x)
  apply h.congr_deriv
  simp only [mul_apply_eq_comp, Pi.add_apply, map_neg, Pi.neg_apply, id_eq, mul_one]
  have hv : (fun y => a*F (d-u) y + generator J (F (d-u)) y - F' (d-u) y) =
      a • F (d-u) + generator J (F (d-u)) - F' (d-u) := rfl
  rw [hv, map_sub, map_add, map_smul]
  change (Real.exp (a*u)*a)*semigroup J u (F (d-u)) x +
    Real.exp (a*u)*(semigroup J u (generator J (F (d-u))) x -
      semigroup J u (F' (d-u)) x) =
    Real.exp (a*u)*(a*semigroup J u (F (d-u)) x +
      semigroup J u (generator J (F (d-u))) x - semigroup J u (F' (d-u)) x)
  ring

lemma semigroup_subsolution_comparison {n : ℕ} (J : Interaction n)
    (F F' : ℝ → Observables n) (hF : ∀ r, HasDerivAt F (F' r) r)
    {d s a : ℝ} (hs : 0 ≤ s)
    (hineq : ∀ r ∈ Set.Icc (d-s) d, ∀ y,
      F' r y - generator J (F r) y ≤ a*F r y) (x : Spin n) :
    F d x ≤ Real.exp (a*s)*semigroup J s (F (d-s)) x := by
  let H (u : ℝ) := Real.exp (a*u)*semigroup J u (F (d-u)) x
  have hD (u : ℝ) := backward_observable_hasDerivAt J F F' hF d a u x
  have hmono : MonotoneOn H (Set.Icc 0 s) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun u _ => (hD u).continuousAt.continuousWithinAt)
      (fun u _ => (hD u).differentiableAt.differentiableWithinAt)
    intro u hu
    have hui : u ∈ Set.Icc (0:ℝ) s := interior_subset hu
    rw [(hD u).deriv]
    exact mul_nonneg (Real.exp_nonneg _) (semigroup_nonneg J u hui.1 _ (fun y => by
      have h := hineq (d-u) ⟨by linarith only [hui.2], by linarith only [hui.1]⟩ y
      linarith only [h]) x)
  have h := hmono ⟨le_rfl, hs⟩ ⟨hs, le_rfl⟩ hs
  simpa [H] using h

lemma gradient_flow_hasDerivAt {n : ℕ} (J : Interaction n) (f : Observables n)
    (r : ℝ) :
    HasDerivAt (fun t => unweightedGradient (semigroup J t f))
      (fun x => deriv (fun t => unweightedGradient (semigroup J t f) x) r) r := by
  apply hasDerivAt_pi.mpr
  intro x
  exact (unweightedGradient_hasDerivAt J f x r).differentiableAt.hasDerivAt

lemma gradient_comparison_of_drift {n : ℕ} (J : Interaction n) (f : Observables n)
    {d s a : ℝ} (hs : 0 ≤ s)
    (hineq : ∀ r ∈ Set.Icc (d-s) d, ∀ y,
      deriv (fun t => unweightedGradient (semigroup J t f) y) r -
        generator J (unweightedGradient (semigroup J r f)) y ≤
          a*unweightedGradient (semigroup J r f) y) (x : Spin n) :
    unweightedGradient (semigroup J d f) x ≤
      Real.exp (a*s)*semigroup J s (unweightedGradient (semigroup J (d-s) f)) x :=
  semigroup_subsolution_comparison J _ _ (gradient_flow_hasDerivAt J f) hs hineq x

lemma gradient_envelope_of_drift {n : ℕ} (J : Interaction n) (f : Observables n)
    {d a B : ℝ} (hd : 0 ≤ d)
    (hineq : ∀ r ∈ Set.Icc (0:ℝ) d, ∀ y,
      deriv (fun t => unweightedGradient (semigroup J t f) y) r -
        generator J (unweightedGradient (semigroup J r f)) y ≤
          a*unweightedGradient (semigroup J r f) y)
    (hB : ∀y, unweightedGradient f y ≤ B) (x : Spin n) :
    unweightedGradient (semigroup J d f) x ≤ Real.exp (a*d)*B := by
  have h := gradient_comparison_of_drift J f (d := d) (s := d) hd
    (by simpa only [sub_self] using hineq) x
  simp only [sub_self, semigroup_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_left (semigroup_le_const J d hd hB x) (Real.exp_nonneg _))

lemma semigroup_subsolution_small_set {n : ℕ} (J : Interaction n)
    (F F' : ℝ → Observables n) (hF : ∀ r, HasDerivAt F (F' r) r)
    (bad : Set (Spin n)) {κ A d₀ T d s q B : ℝ}
    (hκ : 0 ≤ κ) (hA : 0 ≤ A) (hd₀ : 0 ≤ d₀) (hs : 0 ≤ s)
    (hsd : s ≤ d) (hdT : d ≤ T) (hq : 0 ≤ q) (hB : 0 ≤ B)
    (hpos : ∀ r ∈ Set.Icc (0:ℝ) d, ∀ y, 0 ≤ F r y)
    (hineq : ∀ r ∈ Set.Icc (0:ℝ) d, ∀ y,
      F' r y - generator J (F r) y ≤ (-κ + if y ∈ bad then A else 0)*F r y)
    (havoid : ∀ u ∈ Set.Icc d₀ T, ∀ x,
      semigroup J u (fun y => if y ∈ bad then 1 else 0) x ≤ q)
    (hend : ∀y, F (d-s) y ≤ B) (x : Spin n) :
    F d x ≤ Real.exp (A*d₀)*Real.exp (-κ*s)*semigroup J s (F (d-s)) x +
      A*Real.exp (A*d₀)*T*Real.exp (A*T)*q*B := by
  classical
  have hT : 0 ≤ T := hs.trans (hsd.trans hdT)
  have hor (r : ℝ) (hr : r ∈ Set.Icc (0:ℝ) d) (y : Spin n) :
      F' r y - generator J (F r) y ≤ (A-κ)*F r y := by
    refine (hineq r hr y).trans ?_
    apply mul_le_mul_of_nonneg_right _ (hpos r hr y)
    split_ifs <;> linarith only [hA]
  have hbase (v : ℝ) (hv : 0 ≤ v) (hvd : v ≤ d) :
      F d x ≤ Real.exp ((A-κ)*v)*semigroup J v (F (d-v)) x := by
    apply semigroup_subsolution_comparison J F F' hF hv
    intro r hr y
    exact hor r ⟨by linarith only [hr.1, hvd], hr.2⟩ y
  have hspos : 0 ≤ semigroup J s (F (d-s)) x :=
    semigroup_nonneg J s hs _ (hpos (d-s) ⟨sub_nonneg.mpr hsd, by linarith only [hs]⟩) x
  have herr : 0 ≤ A*Real.exp (A*d₀)*T*Real.exp (A*T)*q*B := by positivity
  by_cases hlong : d₀ ≤ s
  · let H (u : ℝ) := Real.exp (-κ*u)*semigroup J u (F (d-u)) x
    let M : ℝ := A*Real.exp (A*T)*q*B
    have hM : 0 ≤ M := by dsimp [M]; positivity
    have henv (u : ℝ) (hu : u ∈ Set.Icc d₀ s) (y : Spin n) :
        F (d-u) y ≤ Real.exp (A*T)*B := by
      have hu0 : 0 ≤ u := hd₀.trans hu.1
      have hus : 0 ≤ s-u := sub_nonneg.mpr hu.2
      have hcmp := semigroup_subsolution_comparison J F F' hF
        (d := d-u) (s := s-u) (a := A-κ) hus (by
          intro r hr z
          apply hor r ⟨by linarith only [hr.1, hsd], by linarith only [hr.2, hu0]⟩ z) y
      rw [show d-u-(s-u) = d-s by ring] at hcmp
      have hconst := semigroup_le_const J (s-u) hus hend y
      have hexp : Real.exp ((A-κ)*(s-u)) ≤ Real.exp (A*T) := by
        apply Real.exp_le_exp.mpr
        nlinarith only [hus, hκ, hA, hs, hsd, hdT, hu0]
      exact hcmp.trans ((mul_le_mul_of_nonneg_left hconst (Real.exp_nonneg _)).trans
        (mul_le_mul_of_nonneg_right hexp hB))
    have hD (u : ℝ) := backward_observable_hasDerivAt J F F' hF d (-κ) u x
    have hderivLower (u : ℝ) (hu : u ∈ Set.Icc d₀ s) :
        -M ≤ deriv H u := by
      have hu0 : 0 ≤ u := hd₀.trans hu.1
      have hru : d-u ∈ Set.Icc (0:ℝ) d :=
        ⟨by linarith only [hu.2, hsd], by linarith only [hu0]⟩
      let bF : Observables n := fun y => if y ∈ bad then F (d-u) y else 0
      have hdual (y : Spin n) :
          -A*bF y ≤ -κ*F (d-u) y + generator J (F (d-u)) y - F' (d-u) y := by
        have h := hineq (d-u) hru y
        dsimp [bF]
        split_ifs at * <;> linarith only [h]
      have hmon := semigroup_mono J hu0 _ _ hdual x
      have heq : (fun y => -A*bF y) = (-A) • bF := rfl
      rw [heq, map_smul] at hmon
      change -A*semigroup J u bF x ≤ _ at hmon
      have hbF : 0 ≤ semigroup J u bF x :=
        semigroup_nonneg J u hu0 _ (fun y => by
          dsimp [bF]; split_ifs <;> first | exact hpos (d-u) hru y | rfl) x
      have hcF (y : Spin n) : bF y ≤
          (Real.exp (A*T)*B)*(if y ∈ bad then 1 else 0) := by
        dsimp [bF]
        split_ifs <;> simp only [mul_one, mul_zero]
        · exact henv u hu y
        · rfl
      have hcbound := semigroup_mono J hu0 _ _ hcF x
      have hceq : (fun y => Real.exp (A*T)*B*(if y ∈ bad then 1 else 0)) =
          (Real.exp (A*T)*B) • (fun y => if y ∈ bad then 1 else 0) := rfl
      rw [hceq, map_smul] at hcbound
      have hcbound' : semigroup J u bF x ≤ Real.exp (A*T)*B*q := by
        apply hcbound.trans
        exact mul_le_mul_of_nonneg_left
          (havoid u ⟨hu.1, hu.2.trans (hsd.trans hdT)⟩ x) (by positivity)
      have he : Real.exp (-κ*u) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [hκ, hu0])
      have hprod : Real.exp (-κ*u)*A*semigroup J u bF x ≤ M := by
        dsimp [M]
        calc
          _ ≤ 1*A*(Real.exp (A*T)*B*q) :=
            mul_le_mul (mul_le_mul_of_nonneg_right he hA) hcbound' hbF (by positivity)
          _ = _ := by ring
      have hbound := mul_le_mul_of_nonneg_left hmon (Real.exp_nonneg (-κ*u))
      rw [(hD u).deriv]
      dsimp [H] at *
      linarith only [hprod, hbound]
    have hmono : MonotoneOn (fun u => H u+M*u) (Set.Icc d₀ s) := by
      have hf (u : ℝ) : HasDerivAt (fun u => H u+M*u) (deriv H u+M) u := by
        have hdH : HasDerivAt H (deriv H u) u := (hD u).differentiableAt.hasDerivAt
        simpa only [Pi.add_apply, id_eq, mul_one] using hdH.fun_add ((hasDerivAt_id u).const_mul M)
      apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
        (fun u _ => (hf u).continuousAt.continuousWithinAt)
        (fun u _ => (hf u).differentiableAt.differentiableWithinAt)
      intro u hu
      rw [(hf u).deriv]
      linarith only [hderivLower u (interior_subset hu)]
    have hhs := hmono ⟨le_rfl, hlong⟩ ⟨hlong, le_rfl⟩ hlong
    have hH : H d₀ ≤ H s+M*T := by
      have h := mul_le_mul_of_nonneg_left (show s-d₀ ≤ T by linarith only [hsd, hdT, hd₀]) hM
      nlinarith only [hhs, h]
    have hstart := hbase d₀ hd₀ (hlong.trans hsd)
    have heq : Real.exp ((A-κ)*d₀)*semigroup J d₀ (F (d-d₀)) x =
        Real.exp (A*d₀)*H d₀ := by
      dsimp [H]
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    rw [heq] at hstart
    calc
      _ ≤ Real.exp (A*d₀)*(H s+M*T) :=
        hstart.trans (mul_le_mul_of_nonneg_left hH (Real.exp_nonneg _))
      _ = _ := by dsimp [H, M]; ring
  · have hshort : s ≤ d₀ := (lt_of_not_ge hlong).le
    have he : Real.exp ((A-κ)*s) ≤ Real.exp (A*d₀)*Real.exp (-κ*s) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      nlinarith only [hA, hshort]
    exact (hbase s hs hsd).trans ((mul_le_mul_of_nonneg_right he hspos).trans
      (le_add_of_nonneg_right herr))

lemma unweightedGradient_nonneg {n : ℕ} (f : Observables n) (x : Spin n) :
    0 ≤ unweightedGradient f x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem gradient_propagation_small_set {n : ℕ} (J : Interaction n)
    (f : Observables n) (bad : Set (Spin n)) {κ A d₀ T d s q B : ℝ}
    (hκ : 0 ≤ κ) (hA : 0 ≤ A) (hd₀ : 0 ≤ d₀) (hs : 0 ≤ s)
    (hsd : s ≤ d) (hdT : d ≤ T) (hq : 0 ≤ q) (hB : 0 ≤ B)
    (hineq : ∀ r ∈ Set.Icc (0:ℝ) d, ∀ y,
      deriv (fun t => unweightedGradient (semigroup J t f) y) r -
        generator J (unweightedGradient (semigroup J r f)) y ≤
          (-κ + if y ∈ bad then A else 0)*unweightedGradient (semigroup J r f) y)
    (havoid : ∀ u ∈ Set.Icc d₀ T, ∀ x,
      semigroup J u (fun y => if y ∈ bad then 1 else 0) x ≤ q)
    (hend : ∀y, unweightedGradient (semigroup J (d-s) f) y ≤ B) (x : Spin n) :
    unweightedGradient (semigroup J d f) x ≤
      Real.exp (A*d₀)*Real.exp (-κ*s)*
        semigroup J s (unweightedGradient (semigroup J (d-s) f)) x +
      A*Real.exp (A*d₀)*T*Real.exp (A*T)*q*B := by
  exact semigroup_subsolution_small_set J _ _ (gradient_flow_hasDerivAt J f) bad
    hκ hA hd₀ hs hsd hdT hq hB
    (fun r _ y => unweightedGradient_nonneg _ y) hineq havoid hend x

lemma tanh_mono : Monotone Real.tanh :=
  monotone_of_deriv_nonneg (fun r => (hasDerivAt_tanh r).differentiableAt)
    (fun r => by rw [(hasDerivAt_tanh r).deriv]; exact (scalarVariance_pos r).le)

lemma gradientWeight_exp_lower {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) :
    Real.exp (-2*|field J x i|) ≤ gradientWeight J x i := by
  let a := |field J x i|
  have hat : 0 ≤ Real.tanh a := by
    simpa only [Real.tanh_zero] using tanh_mono (abs_nonneg (field J x i))
  have hl : Real.exp (-2*a) ≤ 1-Real.tanh a := by
    have h := exp_two_mul_one_sub_tanh a
    have hm := mul_le_mul_of_nonneg_left (show 1 ≤ 1+Real.tanh a by linarith only [hat])
      (Real.exp_nonneg (-2*a))
    calc
      Real.exp (-2*a) = Real.exp (-2*a)*1 := (mul_one _).symm
      _ ≤ Real.exp (-2*a)*(Real.exp (2*a)*(1-Real.tanh a)) := by rwa [h]
      _ = 1-Real.tanh a := by
        rw [← mul_assoc, ← Real.exp_add, show -2*a+2*a=0 by ring, Real.exp_zero, one_mul]
  have hspin : spin x i*Real.tanh (field J x i) ≤ Real.tanh a := by
    unfold spin
    cases x i <;> simp only [Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul]
    · rw [← Real.tanh_neg]
      exact tanh_mono (neg_le_abs (field J x i))
    · exact tanh_mono (le_abs_self (field J x i))
  exact hl.trans (sub_le_sub_left hspin 1)

lemma unweightedGradient_le_exp_weighted {n : ℕ} (J : Interaction n)
    (f : Observables n) (x : Spin n) {H : ℝ}
    (hfields : ∀ i, |field J x i| ≤ H) :
    unweightedGradient f x ≤ Real.exp (2*H)*weightedGradient J f x := by
  have hw (i : Fin n) : 1 ≤ Real.exp (2*H)*gradientWeight J x i := by
    have h := mul_le_mul_of_nonneg_left (gradientWeight_exp_lower J x i)
      (Real.exp_nonneg (2*H))
    have he : 1 ≤ Real.exp (2*H)*Real.exp (-2*|field J x i|) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      linarith only [hfields i]
    exact he.trans h
  unfold unweightedGradient weightedGradient
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  simpa only [one_mul, mul_assoc] using
    mul_le_mul_of_nonneg_right (hw i) (sq_nonneg (halfDiff i f x))

lemma field_gradient_expectation {n : ℕ} (J : Interaction n) (f : Observables n)
    (hf : ∀ y, |f y| ≤ 1) {z H τ : ℝ} (hz : 0 ≤ z)
    (htail : ∀ x, semigroup J z
      (fun y => if ∃ i, H < |field J y i| then 1 else 0) x ≤ τ) (x : Spin n) :
    semigroup J z (unweightedGradient f) x ≤
      Real.exp (2*H)*semigroup J z (weightedGradient J f) x + (n:ℝ)*τ := by
  classical
  have hp (y : Spin n) : unweightedGradient f y ≤
      Real.exp (2*H)*weightedGradient J f y +
        (n:ℝ)*(if ∃ i, H < |field J y i| then 1 else 0) := by
    split_ifs with h
    · have hb := unweightedGradient_le_dim f hf y
      have hw := mul_nonneg (Real.exp_nonneg (2*H)) (weightedGradient_nonneg J f y)
      linarith only [hb, hw]
    · have hb := unweightedGradient_le_exp_weighted J f y
        (fun i => le_of_not_gt (fun hi => h ⟨i,hi⟩))
      simpa only [mul_zero, add_zero] using hb
  have h := semigroup_mono J hz _ _ hp x
  have heq :
      (fun y => Real.exp (2*H)*weightedGradient J f y +
        (n:ℝ)*(if ∃ i, H < |field J y i| then 1 else 0)) =
      Real.exp (2*H) • weightedGradient J f +
        (n:ℝ) • (fun y => if ∃ i, H < |field J y i| then 1 else 0) := rfl
  rw [heq, map_add, map_smul, map_smul] at h
  change semigroup J z (unweightedGradient f) x ≤
      Real.exp (2*H)*semigroup J z (weightedGradient J f) x +
        (n:ℝ)*semigroup J z (fun y => if ∃ i, H < |field J y i| then 1 else 0) x at h
  exact h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (htail x) (Nat.cast_nonneg n)))

lemma backward_gradient_propagation {n : ℕ} (J : Interaction n) (f : Observables n)
    {D u z C κ r : ℝ} (hu : 0 ≤ u)
    (hprop : ∀ y, unweightedGradient (semigroup J (D-u) f) y ≤
      C*Real.exp (-κ*(z-u))*
        semigroup J (z-u) (unweightedGradient (semigroup J (D-z) f)) y + (n:ℝ)*r)
    (x : Spin n) :
    semigroup J u (unweightedGradient (semigroup J (D-u) f)) x ≤
      C*Real.exp (-κ*(z-u))*
        semigroup J z (unweightedGradient (semigroup J (D-z) f)) x + (n:ℝ)*r := by
  have h := semigroup_mono J hu _ _ hprop x
  have heq :
      (fun y => C*Real.exp (-κ*(z-u))*
        semigroup J (z-u) (unweightedGradient (semigroup J (D-z) f)) y + (n:ℝ)*r) =
      (C*Real.exp (-κ*(z-u))) •
        semigroup J (z-u) (unweightedGradient (semigroup J (D-z) f)) +
      (fun _ => (n:ℝ)*r) := rfl
  rw [heq, map_add, map_smul, semigroup_const] at h
  have hsem : semigroup J u (semigroup J (z-u)
      (unweightedGradient (semigroup J (D-z) f))) =
      semigroup J z (unweightedGradient (semigroup J (D-z) f)) := by
    rw [← mul_apply_eq_comp,
      ← semigroup_add, add_sub_cancel]
  change semigroup J u (unweightedGradient (semigroup J (D-u) f)) x ≤
      C*Real.exp (-κ*(z-u))*
        semigroup J u (semigroup J (z-u) (unweightedGradient (semigroup J (D-z) f))) x +
        (n:ℝ)*r at h
  rwa [hsem] at h

lemma energy_comparison_from_gradient {n : ℕ} (J : Interaction n) (f : Observables n)
    (hf : ∀ y, |f y| ≤ 1) {D u z v C κ r H τ : ℝ}
    (hu : 0 ≤ u) (hz : 0 ≤ z) (hzD : z ≤ D) (hv : 0 ≤ v) (hvzu : v ≤ z-u)
    (hC : 0 ≤ C) (hκ : 0 ≤ κ) (hτ : 0 ≤ τ)
    (hprop : ∀ y, unweightedGradient (semigroup J (D-u) f) y ≤
      C*Real.exp (-κ*(z-u))*
        semigroup J (z-u) (unweightedGradient (semigroup J (D-z) f)) y + (n:ℝ)*r)
    (htail : ∀ x, semigroup J z
      (fun y => if ∃ i, H < |field J y i| then 1 else 0) x ≤ τ) (x : Spin n) :
    backwardEnergy J f x D u ≤
      (2*C*Real.exp (-κ*v)*Real.exp (2*H))*backwardEnergy J f x D z +
        (2*(n:ℝ)*r + 2*C*(n:ℝ)*τ) := by
  have hU := backward_gradient_propagation J f hu hprop x
  have hlate := field_gradient_expectation J (semigroup J (D-z) f)
    (semigroup_abs_le J (sub_nonneg.mpr hzD) f hf) hz htail x
  have hΓ : backwardEnergy J f x D u ≤
      2*semigroup J u (unweightedGradient (semigroup J (D-u) f)) x := by
    have h := semigroup_mono J hu _ _
      (weightedGradient_le J (semigroup J (D-u) f)) x
    have heq : (fun y => 2*unweightedGradient (semigroup J (D-u) f) y) =
      (2:ℝ) • unweightedGradient (semigroup J (D-u) f) := rfl
    rw [heq, map_smul] at h
    exact h
  have hpoint := (mul_le_mul_of_nonneg_left hlate
    (show 0 ≤ C*Real.exp (-κ*(z-u)) by positivity))
  have hexp : Real.exp (-κ*(z-u)) ≤ Real.exp (-κ*v) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [hκ, hvzu]
  have heone : Real.exp (-κ*(z-u)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith only [hκ, hvzu, hv]
  have hcoeff := mul_le_mul_of_nonneg_right hexp
    (show 0 ≤ 2*C*Real.exp (2*H)*backwardEnergy J f x D z by
      exact mul_nonneg (by positivity) (backwardEnergy_nonneg J f x D z hz))
  have herror := mul_le_mul_of_nonneg_right heone
    (show 0 ≤ 2*C*(n:ℝ)*τ by positivity)
  change semigroup J z (unweightedGradient (semigroup J (D-z) f)) x ≤
      Real.exp (2*H)*backwardEnergy J f x D z + (n:ℝ)*τ at hlate
  change C*Real.exp (-κ*(z-u))*
      semigroup J z (unweightedGradient (semigroup J (D-z) f)) x ≤
      C*Real.exp (-κ*(z-u))*(Real.exp (2*H)*backwardEnergy J f x D z+(n:ℝ)*τ) at hpoint
  nlinarith only [hU, hΓ, hpoint, hcoeff, herror]

theorem smoothing_of_small_set_gradient {n : ℕ} (g : Disorder n)
    (bad : Set (Spin n)) {κ A d₀ T t s q H τ γ ε : ℝ}
    (hκ : 0 ≤ κ) (hA : 0 ≤ A) (hd₀ : 0 ≤ d₀) (ht : 0 ≤ t) (hs : 0 < s)
    (hT : t+s ≤ T) (hq : 0 ≤ q) (hτ : 0 ≤ τ) (hε : 0 < ε)
    (hoverlap : continuousDistance g t ≤ 1-ε)
    (hgap : ∀ f : Observables n,
      γ*FiniteLaw.variance (mass g 0) f ≤ stationaryEnergy g f)
    (hdrift : ∀ (f : Observables n), ∀ r ∈ Set.Icc (0:ℝ) T, ∀ y,
      deriv (fun v => unweightedGradient (semigroup (coupling g) v f) y) r -
        generator (coupling g) (unweightedGradient (semigroup (coupling g) r f)) y ≤
          (-κ + if y ∈ bad then A else 0)*
            unweightedGradient (semigroup (coupling g) r f) y)
    (havoid : ∀ u ∈ Set.Icc d₀ T, ∀ x,
      semigroup (coupling g) u (fun y => if y ∈ bad then 1 else 0) x ≤ q)
    (hfields : ∀ z ∈ Set.Icc t (t+s), ∀ x, semigroup (coupling g) z
      (fun y => if ∃ i, H < |field (coupling g) y i| then 1 else 0) x ≤ τ) :
    let C := Real.exp (A*d₀)
    let r := A*C*T*Real.exp (A*T)*q
    let a := 2*C*Real.exp (-κ*(s/2))*Real.exp (2*H)
    let R := 2*(n:ℝ)*r+2*C*(n:ℝ)*τ
    continuousDistance g (t+s) ≤
      (Real.sqrt (2*t*(a/s+R))+Real.exp (-γ*s))/(2*Real.sqrt ε) := by
  dsimp only
  apply smoothing_of_energy_comparison g ht hs (by positivity) hε hoverlap hgap
  intro f hf x u hu z hz
  apply energy_comparison_from_gradient (coupling g) f hf hu.1
    (by linarith only [hz.1, ht, hs]) hz.2 (by linarith only [hs])
    (by linarith only [hz.1, hu.2]) (Real.exp_nonneg _) hκ hτ _
    (hfields z ⟨by linarith only [hz.1, hs], hz.2⟩) x
  intro y
  have hd : t+s-u ≤ T := by linarith only [hT, hu.1]
  have h := gradient_propagation_small_set (coupling g) f bad
    (d := t+s-u) (s := z-u) (B := n) hκ hA hd₀
    (by linarith only [hz.1, hu.2, hs])
    (by linarith only [hz.2]) hd hq (Nat.cast_nonneg n)
    (fun r hr y => hdrift f r ⟨hr.1, hr.2.trans hd⟩ y) havoid
    (fun y => unweightedGradient_le_dim _
      (semigroup_abs_le (coupling g) (by linarith only [hz.2]) f hf) y) y
  rw [show t+s-u-(z-u) = t+s-z by ring] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end SKRatio.Calculus

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Dynamics_PositiveLag
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
attribute [-simp] _root_.OAI.SKRatio.Calculus.continuousDistance_zero _root_.OAI.SKRatio.Calculus.continuousKernel_zero _root_.OAI.SKRatio.Calculus.field_reversal _root_.OAI.SKRatio.Calculus.gibbsEuclideanEquiv_apply _root_.OAI.SKRatio.Calculus.lift_scalarEigenfunction _root_.OAI.SKRatio.Calculus.mass_reversal _root_.OAI.SKRatio.Calculus.reversal_reversal _root_.OAI.SKRatio.Calculus.spin_reversal _root_.OAI.SKRatio.Calculus.stationaryPairingCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory Filter
namespace SKRatio.Calculus
attribute [local instance] Classical.propDecidable

lemma dimensionDecay_pos (a : ℝ) (n : ℕ) : 0 < dimensionDecay a n :=
  Real.exp_pos _

lemma dimensionDecay_tendsto_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (dimensionDecay a) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 a ha).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  unfold dimensionDecay
  simpa only [Function.comp_def, Real.rpow_zero, one_mul] using h

lemma log_pow_mul_dimensionDecay_tendsto_zero (k : ℕ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => (Real.log n)^k * dimensionDecay a n) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) a ha).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  simpa only [Function.comp_def, Real.rpow_natCast, dimensionDecay] using h

lemma nat_mul_dimensionDecay {n : ℕ} (hn : 0 < n) (a : ℝ) :
    (n : ℝ) * dimensionDecay a n = dimensionDecay (a - 1) n := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  calc
    _ = Real.exp (Real.log n) * Real.exp (-a * Real.log n) := by
      rw [Real.exp_log hn']; rfl
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

lemma logarithmicVarianceBound_tendsto_zero {κ α : ℝ}
    (hκ : 0 < κ) (hα : 0 < α) (A d₀ D : ℝ) :
    Tendsto (logarithmicVarianceBound κ A d₀ D α) atTop (𝓝 0) := by
  have h1 := (dimensionDecay_tendsto_zero
    (a := κ*α/4) (by positivity)).const_mul (4*D*Real.exp (A*d₀)/α)
  have h2 := (log_pow_mul_dimensionDecay_tendsto_zero 2 (by norm_num : (0:ℝ)<3)).const_mul
    (4*A*D^2*Real.exp (A*d₀))
  have h3 := (log_pow_mul_dimensionDecay_tendsto_zero 1 (by norm_num : (0:ℝ)<3)).const_mul
    (4*D*Real.exp (A*d₀))
  unfold logarithmicVarianceBound
  simpa only [zero_mul, mul_zero, add_zero, pow_one] using
    (h1.add h2).add h3

lemma logarithmicSmoothingBound_tendsto_zero {κ α γ : ℝ}
    (hκ : 0 < κ) (hα : 0 < α) (hγ : 0 < γ) (A d₀ D ε : ℝ) :
    Tendsto (logarithmicSmoothingBound κ A d₀ D α γ ε) atTop (𝓝 0) := by
  have h := (((logarithmicVarianceBound_tendsto_zero hκ hα A d₀ D).sqrt).add
    (dimensionDecay_tendsto_zero (a := γ*α) (by positivity))).div_const (2*Real.sqrt ε)
  unfold logarithmicSmoothingBound
  simpa only [Real.sqrt_zero, zero_add, zero_div] using h

lemma logarithmic_smoothing_of_small_set_gradient {n : ℕ} (hn : 1 < n)
    (g : Disorder n) (bad : Set (Spin n)) {κ A d₀ D α γ ε t : ℝ}
    (hκ : 0 ≤ κ) (hA : 0 ≤ A) (hd₀ : 0 ≤ d₀) (hD : 0 ≤ D)
    (hα : 0 < α) (hε : 0 < ε) (ht : 0 ≤ t)
    (horizon : t+α*Real.log n ≤ D*Real.log n)
    (hoverlap : continuousDistance g t ≤ 1-ε)
    (hgap : ∀ f : Observables n,
      γ*FiniteLaw.variance (mass g 0) f ≤ stationaryEnergy g f)
    (hdrift : ∀ (f : Observables n), ∀ r ∈ Set.Icc (0:ℝ) (D*Real.log n), ∀ y,
      deriv (fun v => unweightedGradient (semigroup (coupling g) v f) y) r -
        generator (coupling g) (unweightedGradient (semigroup (coupling g) r f)) y ≤
          (-κ + if y ∈ bad then A else 0)*
            unweightedGradient (semigroup (coupling g) r f) y)
    (havoid : ∀ u ∈ Set.Icc d₀ (D*Real.log n), ∀ x,
      semigroup (coupling g) u (fun y => if y ∈ bad then 1 else 0) x ≤
        dimensionDecay (A*D+4) n)
    (hfields : ∀ z ∈ Set.Icc t (t+α*Real.log n), ∀ x, semigroup (coupling g) z
      (fun y => if ∃ i, (κ*α/8)*Real.log n < |field (coupling g) y i| then 1 else 0) x ≤
        dimensionDecay 4 n) :
    continuousDistance g (t+α*Real.log n) ≤
      logarithmicSmoothingBound κ A d₀ D α γ ε n := by
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hs : 0 < α*Real.log n := mul_pos hα hlog
  have hsne : α*Real.log n ≠ 0 := ne_of_gt hs
  have h := smoothing_of_small_set_gradient g bad
    hκ hA hd₀ ht hs horizon (dimensionDecay_pos (A*D+4) n).le
    (dimensionDecay_pos 4 n).le hε hoverlap hgap hdrift havoid hfields
  dsimp only at h
  apply h.trans
  apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ 2*Real.sqrt ε)
  have hexpγ : Real.exp (-γ*(α*Real.log n)) = dimensionDecay (γ*α) n := by
    unfold dimensionDecay; congr 1; ring
  change Real.sqrt _ + Real.exp (-γ*(α*Real.log n)) ≤
    Real.sqrt (logarithmicVarianceBound κ A d₀ D α n) + dimensionDecay (γ*α) n
  rw [hexpγ]
  apply add_le_add _ le_rfl
  apply Real.sqrt_le_sqrt
  have htD : t ≤ D*Real.log n := by linarith only [horizon, hs]
  have haexp : Real.exp (-κ*(α*Real.log n/2))*Real.exp (2*((κ*α/8)*Real.log n)) =
      dimensionDecay (κ*α/4) n := by
    rw [← Real.exp_add]; unfold dimensionDecay; congr 1; ring
  have hqexp : Real.exp (A*(D*Real.log n))*dimensionDecay (A*D+4) n =
      dimensionDecay 4 n := by
    unfold dimensionDecay; rw [← Real.exp_add]; congr 1; ring
  have hN : (n:ℝ)*dimensionDecay 4 n = dimensionDecay 3 n := by
    simpa only [show (4:ℝ)-1=3 by norm_num] using nat_mul_dimensionDecay (by omega : 0<n) 4
  have hapos : 0 ≤ 2*Real.exp (A*d₀)*dimensionDecay (κ*α/4) n/(α*Real.log n) +
      (2*(n:ℝ)*(A*Real.exp (A*d₀)*(D*Real.log n)*dimensionDecay 4 n) +
        2*Real.exp (A*d₀)*(n:ℝ)*dimensionDecay 4 n) := by
    dsimp only [dimensionDecay]; positivity
  calc
    _ = 2*t*(2*Real.exp (A*d₀)*dimensionDecay (κ*α/4) n/(α*Real.log n) +
      (2*(n:ℝ)*(A*Real.exp (A*d₀)*(D*Real.log n)*dimensionDecay 4 n) +
        2*Real.exp (A*d₀)*(n:ℝ)*dimensionDecay 4 n)) := by
          rw [mul_assoc (2*Real.exp (A*d₀)), haexp]
          rw [mul_assoc (A*Real.exp (A*d₀)*(D*Real.log n)), hqexp]
    _ ≤ 2*(D*Real.log n)*(2*Real.exp (A*d₀)*dimensionDecay (κ*α/4) n/(α*Real.log n) +
      (2*(n:ℝ)*(A*Real.exp (A*d₀)*(D*Real.log n)*dimensionDecay 4 n) +
        2*Real.exp (A*d₀)*(n:ℝ)*dimensionDecay 4 n)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htD (by norm_num)) hapos
    _ = logarithmicVarianceBound κ A d₀ D α n := by
      have hαne := ne_of_gt hα
      have hlogne := ne_of_gt hlog
      have hregroup : 2*(n:ℝ)*(A*Real.exp (A*d₀)*(D*Real.log n)*dimensionDecay 4 n) +
          2*Real.exp (A*d₀)*(n:ℝ)*dimensionDecay 4 n =
          (2*A*Real.exp (A*d₀)*D*Real.log n+2*Real.exp (A*d₀))*dimensionDecay 3 n := by
        calc
          _ = (2*A*Real.exp (A*d₀)*D*Real.log n+2*Real.exp (A*d₀))*
            ((n:ℝ)*dimensionDecay 4 n) := by ring
          _ = _ := by rw [hN]
      rw [hregroup]
      unfold logarithmicVarianceBound
      field_simp
      ring

theorem uniform_positive_lag_of_small_set_gradient
    (G : ∀ n : ℕ, Set (Disorder n))
    (bad : ∀ n, Disorder n → Set (Spin n)) {κ A d₀ γ : ℝ}
    (hκ : 0 < κ) (hA : 0 ≤ A) (hd₀ : 0 ≤ d₀) (hγ : 0 < γ)
    (hgap : ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ f : Observables n,
      γ*FiniteLaw.variance (mass g 0) f ≤ stationaryEnergy g f)
    (hdrift : ∀ D : ℝ, 0 < D → ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      ∀ (f : Observables n), ∀ r ∈ Set.Icc (0:ℝ) (D*Real.log n), ∀ y,
      deriv (fun v => unweightedGradient (semigroup (coupling g) v f) y) r -
        generator (coupling g) (unweightedGradient (semigroup (coupling g) r f)) y ≤
          (-κ + if y ∈ bad n g then A else 0)*
            unweightedGradient (semigroup (coupling g) r f) y)
    (havoid : ∀ D m : ℝ, 0 < D → 0 < m →
      ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ u ∈ Set.Icc d₀ (D*Real.log n), ∀ x,
      semigroup (coupling g) u (fun y => if y ∈ bad n g then 1 else 0) x ≤ dimensionDecay m n)
    (hfields : ∀ ε δ D m : ℝ, 0 < ε → 0 < δ → 0 < D → 0 < m →
      ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ z ∈ Set.Icc (0:ℝ) (D*Real.log n),
      continuousDistance g z ≤ 1-ε → ∀ x, semigroup (coupling g) z
        (fun y => if ∃ i, δ*Real.log n < |field (coupling g) y i| then 1 else 0) x ≤
          dimensionDecay m n) :
    ∀ ε α D δ : ℝ, 0 < ε → 0 < α → 0 < δ →
      ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ t : ℝ,
      0 ≤ t → t+α*Real.log n ≤ D*Real.log n →
      continuousDistance g t ≤ 1-ε → continuousDistance g (t+α*Real.log n) ≤ δ := by
  intro ε α D δ hε hα hδ
  let D' := max 1 D
  have hD : 0 < D' := lt_of_lt_of_le (by norm_num) (le_max_left 1 D)
  have hm : 0 < A*D'+4 := by positivity
  have hthreshold : 0 < κ*α/8 := by positivity
  have hlim := logarithmicSmoothingBound_tendsto_zero hκ hα hγ A d₀ D' ε
  filter_upwards [hgap, hdrift D' hD, havoid D' (A*D'+4) hD hm,
    hfields ε (κ*α/8) D' 4 hε hthreshold hD (by norm_num),
    hlim.eventually (gt_mem_nhds hδ), eventually_gt_atTop 1]
    with n hngap hndrift hnavoid hnfields hnbound hn
  intro g hg t ht hhor ho
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hhor' : t+α*Real.log n ≤ D'*Real.log n :=
    hhor.trans (mul_le_mul_of_nonneg_right (le_max_right 1 D) hlog.le)
  apply (logarithmic_smoothing_of_small_set_gradient hn g (bad n g)
    hκ.le hA hd₀ hD.le hα hε ht hhor' ho (hngap g hg)
    (hndrift g hg) (hnavoid g hg) ?_).trans hnbound.le
  intro z hz
  apply hnfields g hg z ⟨ht.trans hz.1, hz.2.trans hhor'⟩
  exact (continuousDistance_antitone g ht hz.1).trans ho

end SKRatio.Calculus

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_FieldTails
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
attribute [-simp] _root_.OAI.SKRatio.Calculus.continuousDistance_zero _root_.OAI.SKRatio.Calculus.continuousKernel_zero _root_.OAI.SKRatio.Calculus.gibbsEuclideanEquiv_apply _root_.OAI.SKRatio.Calculus.lift_scalarEigenfunction _root_.OAI.SKRatio.Calculus.stationaryPairingCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory Filter
namespace SKRatio.Calculus
attribute [local instance] Classical.propDecidable

lemma gibbsMean_field_zero {n : ℕ} (g : Disorder n) (i : Fin n) :
    FiniteLaw.mean (mass g 0) (fun x => field (coupling g) x i) = 0 := by
  let e : Spin n ≃ Spin n := Function.Involutive.toPerm reversal (fun x => reversal_reversal x)
  have he := Equiv.sum_comp e (fun x => mass g 0 x * field (coupling g) x i)
  change (∑ x, mass g 0 (reversal x) * field (coupling g) (reversal x) i) = _ at he
  simp only [mass_reversal, field_reversal, mul_neg, Finset.sum_neg_distrib] at he
  unfold FiniteLaw.mean
  linarith only [he]

lemma halfDiff_field {n : ℕ} (J : Interaction n) (i j : Fin n) (x : Spin n) :
    halfDiff j (fun y => field J y i) x = J i j := by
  unfold field
  rw [halfDiff_sum]
  have hlin (l : Fin n) : halfDiff j (fun y => J i l * spin y l) x =
      J i l * halfDiff j (fun y => spin y l) x := by unfold halfDiff; ring
  simp only [hlin, halfDiff_spin, mul_ite, mul_one, mul_zero, Fintype.sum_ite_eq]

lemma unweightedGradient_field {n : ℕ} (J : Interaction n) (i : Fin n) (x : Spin n) :
    unweightedGradient (fun y => field J y i) x = ∑ j, J i j ^ 2 := by
  simp [unweightedGradient, halfDiff_field]

lemma stationary_field_variance_le {n : ℕ} (g : Disorder n) {γ R : ℝ}
    (hγ : 0 < γ) (hrow : ∀ i, ∑ j, coupling g i j ^ 2 ≤ R)
    (hgap : ∀ f : Observables n,
      γ*FiniteLaw.variance (mass g 0) f ≤ stationaryEnergy g f) (i : Fin n) :
    FiniteLaw.variance (mass g 0) (fun y => field (coupling g) y i) ≤ 2*R/γ := by
  apply (le_div_iff₀ hγ).mpr
  have h := hgap (fun y => field (coupling g) y i)
  have hE : stationaryEnergy g (fun y => field (coupling g) y i) ≤ 2*R := by
    unfold stationaryEnergy FiniteLaw.mean
    calc
      _ ≤ ∑ x, mass g 0 x * (2*R) := by
        apply Finset.sum_le_sum
        intro x _
        apply mul_le_mul_of_nonneg_left _ (mass_nonneg g 0 x)
        have hh := weightedGradient_le (coupling g) (fun y => field (coupling g) y i) x
        rw [unweightedGradient_field] at hh
        exact hh.trans (mul_le_mul_of_nonneg_left (hrow i) (by norm_num))
      _ = _ := by rw [← Finset.sum_mul, sum_mass, one_mul]
  linarith only [h, hE]

lemma field_mean_of_overlap {n : ℕ} (g : Disorder n) {t ε V W : ℝ}
    (ht : 0 ≤ t) (hε : 0 < ε) (hoverlap : continuousDistance g t ≤ 1-ε)
    (hvar : ∀ x i, FiniteLaw.variance (continuousKernel (coupling g) t x)
      (fun y => field (coupling g) y i) ≤ V)
    (hstat : ∀ i, FiniteLaw.variance (mass g 0) (fun y => field (coupling g) y i) ≤ W)
    (x : Spin n) (i : Fin n) :
    |semigroup (coupling g) t (fun y => field (coupling g) y i) x| ≤
      (Real.sqrt V+Real.sqrt W)/Real.sqrt ε := by
  have h := FiniteLaw.common_mass_means (continuousKernel (coupling g) t x) (mass g 0)
    (fun y => field (coupling g) y i)
    (continuousKernel_nonneg _ t ht x) (mass_nonneg g 0)
    (continuousKernel_sum _ t x) (sum_mass g 0) hε
    ((tv_le_continuousDistance g t x).trans hoverlap)
  rw [gibbsMean_field_zero, sub_zero] at h
  rw [← semigroup_eq_kernel] at h
  exact h.trans (div_le_div_of_nonneg_right
    (add_le_add (Real.sqrt_le_sqrt (hvar x i)) (Real.sqrt_le_sqrt (hstat i)))
      (Real.sqrt_nonneg _))

lemma exp_abs_le_sum (z : ℝ) : Real.exp |z| ≤ Real.exp z + Real.exp (-z) := by
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz]
    linarith [Real.exp_pos (-z)]
  · rw [abs_of_nonpos hz]
    linarith [Real.exp_pos z]

lemma indicator_max_le_exp {n : ℕ} (u c : Fin n → ℝ) {θ H m : ℝ}
    (hθ : 0 ≤ θ) (hc : ∀ i, |c i| ≤ m) :
    (if ∃ i, H < |u i| then (1:ℝ) else 0) ≤
      Real.exp (-θ*(H-m)) * ∑ i, (Real.exp (θ*(u i-c i)) + Real.exp (-θ*(u i-c i))) := by
  classical
  by_cases hu : ∃ i, H < |u i|
  · simp only [hu, ↓reduceIte]
    obtain ⟨i, hi⟩ := hu
    have htri : H-m ≤ |u i-c i| := by
      have hh : |u i| ≤ |u i-c i|+|c i| := by
        simpa only [sub_add_cancel] using abs_add_le (u i-c i) (c i)
      linarith [hc i]
    have hs : Real.exp (θ*|u i-c i|) ≤
        ∑ j, (Real.exp (θ*(u j-c j)) + Real.exp (-θ*(u j-c j))) := by
      have hh := exp_abs_le_sum (θ*(u i-c i))
      rw [abs_mul, abs_of_nonneg hθ] at hh
      have hh' : Real.exp (θ*|u i-c i|) ≤
          Real.exp (θ*(u i-c i))+Real.exp (-θ*(u i-c i)) := by
        simpa only [neg_mul] using hh
      exact hh'.trans (Finset.single_le_sum (f := fun j =>
        Real.exp (θ*(u j-c j))+Real.exp (-θ*(u j-c j)))
        (fun j _ => by positivity) (Finset.mem_univ i))
    calc
      1 ≤ Real.exp (-θ*(H-m))*Real.exp (θ*|u i-c i|) := by
        rw [← Real.exp_add, Real.one_le_exp_iff]
        have hh := mul_le_mul_of_nonneg_left htri hθ
        linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
  · simp only [hu, ↓reduceIte]
    positivity

lemma semigroup_max_tail {n : ℕ} (J : Interaction n) (f : Fin n → Observables n)
    {t θ H m C : ℝ} (ht : 0 ≤ t) (hθ : 0 ≤ θ) (x : Spin n)
    (hmean : ∀ i, |semigroup J t (f i) x| ≤ m)
    (hmgf : ∀ i, ∀ σ ∈ ({-1,1}:Set ℝ),
      semigroup J t (fun y => Real.exp (σ*θ*(f i y-semigroup J t (f i) x))) x ≤ C) :
    semigroup J t (fun y => if ∃ i, H < |f i y| then (1:ℝ) else 0) x ≤
      2*(n:ℝ)*C*Real.exp (-θ*(H-m)) := by
  classical
  have hh := semigroup_mono J ht _ _ (fun y =>
    indicator_max_le_exp (fun i => f i y) (fun i => semigroup J t (f i) x) (H := H) hθ hmean) x
  have he : (fun y => Real.exp (-θ*(H-m))*∑ i,
      (Real.exp (θ*(f i y-semigroup J t (f i) x)) +
       Real.exp (-θ*(f i y-semigroup J t (f i) x)))) =
      Real.exp (-θ*(H-m)) • ∑ i : Fin n,
        ((fun y => Real.exp (θ*(f i y-semigroup J t (f i) x))) +
         (fun y => Real.exp (-θ*(f i y-semigroup J t (f i) x)))) := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.add_apply]
  rw [he, map_smul, map_sum] at hh
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, map_add, Pi.add_apply] at hh
  have hib : ∀ i : Fin n,
      semigroup J t (fun y => Real.exp (θ*(f i y-semigroup J t (f i) x))) x +
      semigroup J t (fun y => Real.exp (-θ*(f i y-semigroup J t (f i) x))) x ≤ 2*C := by
    intro i
    have hpos := hmgf i 1 (by simp)
    have hneg := hmgf i (-1) (by simp)
    simp only [one_mul, neg_one_mul] at hpos hneg
    linarith
  calc
    _ ≤ _ := hh
    _ ≤ Real.exp (-θ*(H-m))*∑ _i : Fin n, 2*C :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hib i)) (Real.exp_pos _).le
    _ = _ := by simp; ring

theorem uniform_field_tails_of_moments
    (G : ∀ n : ℕ, Set (Disorder n)) {V W : ℝ}
    (hstat : ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ i,
      FiniteLaw.variance (mass g 0) (fun y => field (coupling g) y i) ≤ W)
    (hvar : ∀ D : ℝ, 0 < D → ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      ∀ t ∈ Set.Icc (0:ℝ) (D*Real.log n), ∀ x i,
      FiniteLaw.variance (continuousKernel (coupling g) t x)
        (fun y => field (coupling g) y i) ≤ V)
    (hmgf : ∀ D θ : ℝ, 0 < D → 0 < θ → ∃ M : ℝ,
      ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ t ∈ Set.Icc (0:ℝ) (D*Real.log n),
      ∀ x i, ∀ σ ∈ ({-1,1}:Set ℝ), semigroup (coupling g) t
        (fun y => Real.exp (σ*θ*(field (coupling g) y i-
          semigroup (coupling g) t (fun z => field (coupling g) z i) x))) x ≤ M) :
    ∀ ε δ D m : ℝ, 0 < ε → 0 < δ → 0 < D → 0 < m →
      ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ t ∈ Set.Icc (0:ℝ) (D*Real.log n),
      continuousDistance g t ≤ 1-ε → ∀ x, semigroup (coupling g) t
        (fun y => if ∃ i, δ*Real.log n < |field (coupling g) y i| then 1 else 0) x ≤
          dimensionDecay m n := by
  intro ε δ D m hε hδ hD hm
  let θ := (m+2)/δ
  have hθ : 0 < θ := div_pos (by linarith only [hm]) hδ
  have hθδ : θ*δ = m+2 := div_mul_cancel₀ _ (ne_of_gt hδ)
  let B := (Real.sqrt V+Real.sqrt W)/Real.sqrt ε
  obtain ⟨M,hM⟩ := hmgf D θ hD hθ
  have herr := (dimensionDecay_tendsto_zero (by norm_num : (0:ℝ)<1)).const_mul
    (2*M*Real.exp (θ*B))
  simp only [mul_zero] at herr
  have herr' : ∀ᶠ n : ℕ in atTop,
      (2*M*Real.exp (θ*B))*dimensionDecay 1 n ≤ 1 := by
    filter_upwards [herr.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with n hn
    simpa only [mul_zero] using hn.le
  filter_upwards [hstat,hvar D hD,hM,herr',eventually_gt_atTop 0]
    with n hnstat hnvar hnmgf hnerr hn
  intro g hg t ht ho x
  have hmean := field_mean_of_overlap g ht.1 hε ho (hnvar g hg t ht) (hnstat g hg) x
  have h := semigroup_max_tail (coupling g) (fun i y => field (coupling g) y i)
    (H := δ*Real.log n) ht.1 hθ.le x hmean (hnmgf g hg t ht x)
  have he : 2*(n:ℝ)*M*Real.exp (-θ*(δ*Real.log n-B)) =
      ((2*M*Real.exp (θ*B))*dimensionDecay 1 n)*dimensionDecay m n := by
    have he' : Real.exp (-θ*(δ*Real.log n-B)) =
        Real.exp (θ*B)*dimensionDecay (m+2) n := by
      unfold dimensionDecay
      rw [← Real.exp_add]
      congr 1
      calc
        _ = θ*B-(θ*δ)*Real.log n := by ring
        _ = _ := by rw [hθδ]; ring
    rw [he']
    calc
      _ = (2*M*Real.exp (θ*B))*((n:ℝ)*dimensionDecay (m+2) n) := by ring
      _ = (2*M*Real.exp (θ*B))*dimensionDecay (m+2-1) n := by
        rw [nat_mul_dimensionDecay hn]
      _ = (2*M*Real.exp (θ*B))*(dimensionDecay 1 n*dimensionDecay m n) := by
        congr 1
        unfold dimensionDecay
        rw [← Real.exp_add]
        congr 1
        ring
      _ = _ := by ring
  change _ ≤ 2*(n:ℝ)*M*Real.exp (-θ*(δ*Real.log n-B)) at h
  rw [he] at h
  exact h.trans (by simpa only [one_mul] using
    (mul_le_mul_of_nonneg_right hnerr (dimensionDecay_pos m n).le))

end SKRatio.Calculus

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_GradientMoments
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
attribute [-simp] _root_.OAI.SKRatio.Calculus.continuousDistance_zero _root_.OAI.SKRatio.Calculus.continuousKernel_zero _root_.OAI.SKRatio.Calculus.gibbsEuclideanEquiv_apply _root_.OAI.SKRatio.Calculus.lift_scalarEigenfunction _root_.OAI.SKRatio.Calculus.stationaryPairingCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory Filter
namespace SKRatio.Calculus
attribute [local instance] Classical.propDecidable

lemma integral_exp_decay_le {κ d : ℝ} (hκ : 0 < κ) :
    (∫ r in (0:ℝ)..d, Real.exp (-κ*r)) ≤ 1/κ := by
  have hd (r : ℝ) : HasDerivAt (fun r : ℝ => -Real.exp (-κ*r)/κ)
      (Real.exp (-κ*r)) r := by
    have h := (((hasDerivAt_id r).const_mul (-κ)).exp.neg).div_const κ
    apply h.congr_deriv
    simp only [mul_one, id_eq]
    field_simp
  have hi : IntervalIntegrable (fun r : ℝ => Real.exp (-κ*r)) volume 0 d :=
    (by fun_prop : Continuous (fun r : ℝ => Real.exp (-κ*r))).intervalIntegrable 0 d
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r) hi]
  simp only [mul_zero, Real.exp_zero, neg_div]
  have hp := div_nonneg (Real.exp_nonneg (-κ*d)) hκ.le
  linarith

lemma gradient_envelope_bounds {κ C E R d : ℝ}
    (hκ : 0 < κ) (hC : 0 ≤ C) (hR : 0 ≤ R) (hd : 0 ≤ d)
    (hE : E ≤ 1) (hdE : d*E ≤ 1) :
    (∀ r ∈ Set.Icc (0:ℝ) d, R*(C*Real.exp (-κ*r)+E) ≤ R*(C+1)) ∧
    (∫ r in (0:ℝ)..d, R*(C*Real.exp (-κ*r)+E)) ≤ R*(C/κ+1) := by
  refine ⟨?_,?_⟩
  · intro r hr
    apply mul_le_mul_of_nonneg_left _ hR
    have he : Real.exp (-κ*r) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [hκ,hr.1])
    have hc := mul_le_mul_of_nonneg_left he hC
    linarith
  · have hi : IntervalIntegrable (fun r : ℝ => C*Real.exp (-κ*r)) volume 0 d :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hd).mpr
        (by fun_prop : Continuous (fun r : ℝ => C*Real.exp (-κ*r))).integrableOn_Icc
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hi intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    apply mul_le_mul_of_nonneg_left _ hR
    have hu := mul_le_mul_of_nonneg_left (integral_exp_decay_le (d := d) hκ) hC
    simpa only [mul_one_div] using add_le_add hu hdE

lemma moments_of_gradient_envelope {n : ℕ} (J : Interaction n) (f : Observables n)
    {κ C E R d : ℝ} (hκ : 0 < κ) (hC : 0 ≤ C) (hR : 0 ≤ R) (hd : 0 ≤ d)
    (hE : E ≤ 1) (hdE : d*E ≤ 1)
    (henv : ∀ r ∈ Set.Icc (0:ℝ) d, ∀ x,
      unweightedGradient (semigroup J r f) x ≤ R*(C*Real.exp (-κ*r)+E)) :
    (∀ x, FiniteLaw.variance (continuousKernel J d x) f ≤ 4*(R*(C/κ+1))) ∧
    (∀ θ x, semigroup J d (fun y => Real.exp (θ*(f y-semigroup J d f x))) x ≤
      Real.exp (2*θ^2*Real.exp (2*|θ| *Real.sqrt (R*(C+1)))*(R*(C/κ+1)))) := by
  have hb : IntervalIntegrable (fun r : ℝ => R*(C*Real.exp (-κ*r)+E)) volume 0 d :=
    (by fun_prop : Continuous (fun r : ℝ => R*(C*Real.exp (-κ*r)+E))).intervalIntegrable 0 d
  have ⟨hB,hI⟩ := gradient_envelope_bounds hκ hC hR hd hE hdE
  constructor
  · intro x
    rw [FiniteLaw.variance_eq _ _ (continuousKernel_sum J d x), ← semigroup_eq_kernel,
      ← semigroup_eq_kernel]
    exact (semigroup_variance_le J f d hd _ hb henv x).trans
      (mul_le_mul_of_nonneg_left hI (by norm_num))
  · intro θ x
    exact (semigroup_jump_mgf J f d hd _ (R*(C+1)) θ hb hB henv x).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hI (by positivity)))

lemma gradient_envelope_of_small_set {n : ℕ} (J : Interaction n)
    (f : Observables n) (bad : Set (Spin n)) {κ A d₀ T q R : ℝ}
    (hκ : 0 ≤ κ) (hA : 0 ≤ A) (hd₀ : 0 ≤ d₀) (hq : 0 ≤ q) (hR : 0 ≤ R)
    (hinit : ∀ y, unweightedGradient f y ≤ R)
    (hdrift : ∀ r ∈ Set.Icc (0:ℝ) T, ∀ y,
      deriv (fun v => unweightedGradient (semigroup J v f) y) r -
        generator J (unweightedGradient (semigroup J r f)) y ≤
          (-κ + if y ∈ bad then A else 0)*unweightedGradient (semigroup J r f) y)
    (havoid : ∀ u ∈ Set.Icc d₀ T, ∀ x,
      semigroup J u (fun y => if y ∈ bad then 1 else 0) x ≤ q)
    (r : ℝ) (hr : r ∈ Set.Icc (0:ℝ) T) (x : Spin n) :
    unweightedGradient (semigroup J r f) x ≤
      R*(Real.exp (A*d₀)*Real.exp (-κ*r)+A*Real.exp (A*d₀)*T*Real.exp (A*T)*q) := by
  have h := gradient_propagation_small_set J f bad hκ hA hd₀ hr.1 le_rfl hr.2 hq hR
    (fun v hv => hdrift v ⟨hv.1,hv.2.trans hr.2⟩) havoid
    (by simpa only [sub_self,semigroup_zero,one_apply_eq_self] using hinit) x
  simp only [sub_self,semigroup_zero,one_apply_eq_self] at h
  calc
    _ ≤ _ := h
    _ ≤ Real.exp (A*d₀)*Real.exp (-κ*r)*R +
        A*Real.exp (A*d₀)*T*Real.exp (A*T)*q*R :=
      add_le_add (mul_le_mul_of_nonneg_left
        (semigroup_le_const J r hr.1 hinit x) (by positivity)) le_rfl
    _ = _ := by ring

theorem uniform_gradient_moments_of_small_set
    (G : ∀ n : ℕ, Set (Disorder n))
    (bad : ∀ n, Disorder n → Set (Spin n)) {κ A d₀ : ℝ}
    (hκ : 0 < κ) (hA : 0 ≤ A) (hd₀ : 0 ≤ d₀)
    (hdrift : ∀ D : ℝ, 0 < D → ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      ∀ (f : Observables n), ∀ r ∈ Set.Icc (0:ℝ) (D*Real.log n), ∀ y,
      deriv (fun v => unweightedGradient (semigroup (coupling g) v f) y) r -
        generator (coupling g) (unweightedGradient (semigroup (coupling g) r f)) y ≤
          (-κ + if y ∈ bad n g then A else 0)*
            unweightedGradient (semigroup (coupling g) r f) y)
    (havoid : ∀ D m : ℝ, 0 < D → 0 < m →
      ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ u ∈ Set.Icc d₀ (D*Real.log n), ∀ x,
      semigroup (coupling g) u (fun y => if y ∈ bad n g then 1 else 0) x ≤ dimensionDecay m n)
    {D R : ℝ} (hD : 0 < D) (hR : 0 ≤ R) :
    ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ f : Observables n,
      (∀ y, unweightedGradient f y ≤ R) → ∀ d ∈ Set.Icc (0:ℝ) (D*Real.log n),
      (∀ x, FiniteLaw.variance (continuousKernel (coupling g) d x) f ≤
        4*(R*(Real.exp (A*d₀)/κ+1))) ∧
      (∀ θ x, semigroup (coupling g) d (fun y => Real.exp
        (θ*(f y-semigroup (coupling g) d f x))) x ≤
          Real.exp (2*θ^2*Real.exp (2*|θ| *Real.sqrt (R*(Real.exp (A*d₀)+1)))*
            (R*(Real.exp (A*d₀)/κ+1)))) := by
  let C := Real.exp (A*d₀)
  let E (n : ℕ) := A*C*D*(Real.log n)*dimensionDecay 4 n
  have hEn : Tendsto E atTop (𝓝 0) := by
    have h := (log_pow_mul_dimensionDecay_tendsto_zero 1 (by norm_num : (0:ℝ)<4)).const_mul (A*C*D)
    simpa only [pow_one, mul_zero, mul_assoc, E] using h
  have hTEn : Tendsto (fun n : ℕ => (D*Real.log n)*E n) atTop (𝓝 0) := by
    have h := (log_pow_mul_dimensionDecay_tendsto_zero 2 (by norm_num : (0:ℝ)<4)).const_mul (A*C*D^2)
    simp only [mul_zero] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    dsimp only [E]
    ring
  have hm : 0 < A*D+4 := by positivity
  filter_upwards [hdrift D hD,havoid D (A*D+4) hD hm,
    hEn.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)),
    hTEn.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)),eventually_ge_atTop 1]
    with n hndrift hnavoid hnE hnTE hn
  intro g hg f hf d hd
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hE0 : 0 ≤ E n := by dsimp [E,C,dimensionDecay]; positivity
  have herror : A*Real.exp (A*d₀)*(D*Real.log n)*Real.exp (A*(D*Real.log n))*
      dimensionDecay (A*D+4) n = E n := by
    have hprod : Real.exp (A*(D*Real.log n))*dimensionDecay (A*D+4) n = dimensionDecay 4 n := by
      unfold dimensionDecay
      rw [← Real.exp_add]
      congr 1
      ring
    rw [mul_assoc (A*Real.exp (A*d₀)*(D*Real.log n)),hprod]
    dsimp only [E,C]
    ring
  apply moments_of_gradient_envelope (coupling g) f hκ (Real.exp_nonneg _) hR hd.1 hnE.le
    ((mul_le_mul_of_nonneg_right hd.2 hE0).trans hnTE.le)
  intro r hr x
  have h := gradient_envelope_of_small_set (coupling g) f (bad n g)
    hκ.le hA hd₀ (dimensionDecay_pos (A*D+4) n).le hR hf
    (hndrift g hg f) (hnavoid g hg) r ⟨hr.1,hr.2.trans hd.2⟩ x
  rwa [herror] at h

lemma row_squares_le_opNorm {n : ℕ} (J : Interaction n)
    (hsymm : ∀ i j, J i j = J j i) {K : ℝ}
    (hK : 0 ≤ K)
    (hop : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) J‖ ≤ K) (i : Fin n) :
    ∑ j, J i j ^ 2 ≤ K^2 := by
  let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i 1
  have he : ‖e‖ = 1 := by simp [e]
  have h := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) J).le_opNorm e
  rw [he,mul_one] at h
  have hsq := sq_le_sq₀ (norm_nonneg _) hK |>.mpr (h.trans hop)
  rw [EuclideanSpace.real_norm_sq_eq] at hsq
  have happly (j : Fin n) :
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) J e).ofLp j = J i j := by
    change (∑ coordinate, J j coordinate * e.ofLp coordinate) = J i j
    simp only [e, EuclideanSpace.single, PiLp.single_apply,
      mul_ite, mul_one, mul_zero]
    simp [hsymm j i]
  simpa only [happly] using hsq

theorem uniform_field_tails_of_small_set
    (G : ∀ n : ℕ, Set (Disorder n))
    (bad : ∀ n, Disorder n → Set (Spin n)) {κ A d₀ γ R : ℝ}
    (hκ : 0 < κ) (hA : 0 ≤ A) (hd₀ : 0 ≤ d₀) (hγ : 0 < γ) (hR : 0 ≤ R)
    (hrow : ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ i, ∑ j, coupling g i j ^ 2 ≤ R)
    (hgap : ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ f : Observables n,
      γ*FiniteLaw.variance (mass g 0) f ≤ stationaryEnergy g f)
    (hdrift : ∀ D : ℝ, 0 < D → ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      ∀ (f : Observables n), ∀ r ∈ Set.Icc (0:ℝ) (D*Real.log n), ∀ y,
      deriv (fun v => unweightedGradient (semigroup (coupling g) v f) y) r -
        generator (coupling g) (unweightedGradient (semigroup (coupling g) r f)) y ≤
          (-κ + if y ∈ bad n g then A else 0)*
            unweightedGradient (semigroup (coupling g) r f) y)
    (havoid : ∀ D m : ℝ, 0 < D → 0 < m →
      ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ u ∈ Set.Icc d₀ (D*Real.log n), ∀ x,
      semigroup (coupling g) u (fun y => if y ∈ bad n g then 1 else 0) x ≤ dimensionDecay m n) :
    ∀ ε δ D m : ℝ, 0 < ε → 0 < δ → 0 < D → 0 < m →
      ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ t ∈ Set.Icc (0:ℝ) (D*Real.log n),
      continuousDistance g t ≤ 1-ε → ∀ x, semigroup (coupling g) t
        (fun y => if ∃ i, δ*Real.log n < |field (coupling g) y i| then 1 else 0) x ≤
          dimensionDecay m n := by
  have hmom {D : ℝ} (hD : 0 < D) :=
    uniform_gradient_moments_of_small_set G bad hκ hA hd₀ hdrift havoid hD hR
  apply uniform_field_tails_of_moments (V := 4*(R*(Real.exp (A*d₀)/κ+1)))
    (W := 2*R/γ) G
  · filter_upwards [hrow,hgap] with n hnrow hngap
    intro g hg i
    exact stationary_field_variance_le g hγ (hnrow g hg) (hngap g hg) i
  · intro D hD
    filter_upwards [hrow,hmom hD] with n hnrow hnmom
    intro g hg t ht x i
    exact (hnmom g hg (fun y => field (coupling g) y i)
      (fun y => by rw [unweightedGradient_field]; exact hnrow g hg i) t ht).1 x
  · intro D θ hD hθ
    refine ⟨Real.exp (2*θ^2*Real.exp (2*θ*Real.sqrt (R*(Real.exp (A*d₀)+1)))*
      (R*(Real.exp (A*d₀)/κ+1))),?_⟩
    filter_upwards [hrow,hmom hD] with n hnrow hnmom
    intro g hg t ht x i σ hσ
    have h := (hnmom g hg (fun y => field (coupling g) y i)
      (fun y => by rw [unweightedGradient_field]; exact hnrow g hg i) t ht).2 (σ*θ) x
    rcases hσ with hσ | hσ <;> rcases hσ with rfl
    · simpa only [neg_one_mul, neg_sq, abs_neg, abs_of_pos hθ] using h
    · simpa only [one_mul, abs_of_pos hθ] using h

end SKRatio.Calculus

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_FiniteChain_DiscreteDistanceNonneg
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology _root_.OAI.SKRatioGaussian.instNonemptyUnitBall
attribute [-simp] _root_.OAI.SKRatio.Calculus.abs_signConjugate _root_.OAI.SKRatio.Calculus.abs_spin _root_.OAI.SKRatio.Calculus.attempt_const _root_.OAI.SKRatio.Calculus.attempt_pow_const _root_.OAI.SKRatio.Calculus.continuousDistance_zero _root_.OAI.SKRatio.Calculus.continuousKernel_zero _root_.OAI.SKRatio.Calculus.field_reversal _root_.OAI.SKRatio.Calculus.generator_const _root_.OAI.SKRatio.Calculus.gibbsEuclideanEquiv_apply _root_.OAI.SKRatio.Calculus.gibbsMeanCLM_apply _root_.OAI.SKRatio.Calculus.halfDiff_const _root_.OAI.SKRatio.Calculus.halfDiff_replace _root_.OAI.SKRatio.Calculus.halfDiff_self _root_.OAI.SKRatio.Calculus.halfDiff_spin _root_.OAI.SKRatio.Calculus.lift_scalarEigenfunction _root_.OAI.SKRatio.Calculus.mass_reversal _root_.OAI.SKRatio.Calculus.norm_signedVector _root_.OAI.SKRatio.Calculus.plus_signProduct _root_.OAI.SKRatio.Calculus.replace_replace _root_.OAI.SKRatio.Calculus.replace_same _root_.OAI.SKRatio.Calculus.replace_self _root_.OAI.SKRatio.Calculus.reversal_reversal _root_.OAI.SKRatio.Calculus.semigroup_const _root_.OAI.SKRatio.Calculus.semigroup_zero _root_.OAI.SKRatio.Calculus.signConjugate_twice _root_.OAI.SKRatio.Calculus.signProduct_plus _root_.OAI.SKRatio.Calculus.siteRefresh_const _root_.OAI.SKRatio.Calculus.spin_reversal _root_.OAI.SKRatio.Calculus.spin_sq _root_.OAI.SKRatio.Calculus.stationaryPairingCLM_apply _root_.OAI.SKRatio.Independent.coupling_zero _root_.OAI.SKRatio.Independent.mass_zero _root_.OAI.SKRatio.Independent.siteKernel_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter
namespace SKRatio
section MixingTime
variable {n : ℕ}

theorem discreteDistance_nonneg (g : Disorder n) (k : ℕ) :
    0 ≤ discreteDistance g k :=
  (totalVariation_nonneg _ _).trans (tv_le_discreteDistance g k (fun _ => true))

theorem discreteDistance_le_one (g : Disorder n) (k : ℕ) :
    discreteDistance g k ≤ 1 := by
  apply Finset.sup'_le
  intro x _
  have hP := transition_pow_stochastic g k
  exact totalVariation_le_one _ _ (hP.1 x) (mass_nonneg g 0)
    (Matrix.sum_row_of_mem_rowStochastic hP x) (sum_mass g 0)

theorem discreteDistance_antitone (g : Disorder n) : Antitone (discreteDistance g) := by
  apply antitone_nat_of_succ_le
  intro k
  apply Finset.sup'_le
  intro x _
  have hsum : (∑ y, (transition g ^ k) x y) = ∑ y, mass g 0 y := by
    rw [Matrix.sum_row_of_mem_rowStochastic (transition_pow_stochastic g k), sum_mass]
  calc
    totalVariation ((transition g ^ (k + 1)) x) (mass g 0) =
        totalVariation ((transition g ^ k) x ᵥ* transition g) (mass g 0 ᵥ* transition g) := by
      rw [pow_succ, Matrix.mul_apply_eq_vecMul, transition_stationary]
    _ ≤ totalVariation ((transition g ^ k) x) (mass g 0) :=
      totalVariation_contract _ (transition_stochastic g) _ _ hsum
    _ ≤ discreteDistance g k := tv_le_discreteDistance g k x

theorem exists_geometric_bound (g : Disorder n) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ k : ℕ, discreteDistance g (n * k) ≤ r ^ k := by
  obtain ⟨r, hr0, hr1, hbound⟩ := exists_geometric_block_bound
    (transition g) (transition_stochastic g) (mass g 0) (mass_nonneg g 0) (sum_mass g 0)
    n (transition_n_pos g) (transition_pow_stationary g n)
  refine ⟨r, hr0, hr1, fun k => Finset.sup'_le _ _ (fun x _ => hbound k x)⟩

theorem exists_mixing_time (g : Disorder n) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, discreteDistance g k ≤ ε := by
  obtain ⟨r, hr0, hr1, hbound⟩ := exists_geometric_bound g
  have H := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).eventually (gt_mem_nhds hε)
  obtain ⟨k, hk⟩ := H.exists
  exact ⟨n * k, (hbound k).trans hk.le⟩

theorem mixingTime_spec (g : Disorder n) {ε : ℝ} (hε : 0 < ε) :
    discreteDistance g (mixingTime g ε) ≤ ε :=
  Nat.sInf_mem (exists_mixing_time g hε)

theorem mixingTime_le_of_distance_le (g : Disorder n) {ε : ℝ} {k : ℕ}
    (hk : discreteDistance g k ≤ ε) : mixingTime g ε ≤ k := Nat.sInf_le hk

theorem mixingTime_le_iff (g : Disorder n) {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    mixingTime g ε ≤ k ↔ discreteDistance g k ≤ ε := by
  constructor
  · intro h
    exact (discreteDistance_antitone g h).trans (mixingTime_spec g hε)
  · exact mixingTime_le_of_distance_le g

theorem lt_mixingTime_of_lt_distance (g : Disorder n) {ε : ℝ} (hε : 0 < ε)
    {k : ℕ} (hk : ε < discreteDistance g k) : k < mixingTime g ε := by
  exact lt_of_not_ge (fun h => not_le_of_gt hk ((mixingTime_le_iff g hε k).mp h))

theorem discreteDistance_zero_lower (g : Disorder n) :
    1 - (1 / 2 : ℝ) ^ n ≤ discreteDistance g 0 := by
  have hpoint (x : Spin n) : 1 - mass g 0 x ≤ discreteDistance g 0 := by
    have h := tv_le_discreteDistance g 0 x
    simpa only [pow_zero, totalVariation_dirac _ (mass_nonneg g 0) (sum_mass g 0)] using h
  have hsum : (Fintype.card (Spin n) : ℝ) * (1 - discreteDistance g 0) ≤ 1 := by
    calc
      (Fintype.card (Spin n) : ℝ) * (1 - discreteDistance g 0) =
          ∑ _x : Spin n, (1 - discreteDistance g 0) := by
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ∑ x, mass g 0 x := Finset.sum_le_sum (fun x _ => by linarith [hpoint x])
      _ = 1 := sum_mass g 0
  have hcard : Fintype.card (Spin n) = 2 ^ n := by simp [Spin]
  have hcpos : (0 : ℝ) < Fintype.card (Spin n) := Nat.cast_pos.mpr Fintype.card_pos
  have h : 1 - discreteDistance g 0 ≤ (1 : ℝ) / Fintype.card (Spin n) :=
    (le_div_iff₀ hcpos).mpr (by simpa only [mul_comm] using hsum)
  have hid : (1 : ℝ) / Fintype.card (Spin n) = (1 / 2 : ℝ) ^ n := by
    rw [hcard, Nat.cast_pow, Nat.cast_ofNat, one_div_pow]
  rw [hid] at h
  linarith

theorem denominator_eventually_positive (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ g : Disorder n, 0 < mixingTime g (1 - ε) := by
  have H := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).eventually
    (gt_mem_nhds hε0)
  filter_upwards [H] with n hn
  intro g
  apply lt_mixingTime_of_lt_distance g (sub_pos.mpr hε1)
  linarith [discreteDistance_zero_lower g]

theorem mixing_ratio_bound (g : Disorder n) {ε b T : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (hb0 : 0 < b) (hb1 : b < 1) (hT : 0 < T)
    (hlower : 1 - ε < discreteDistance g ⌊(1 - b) * T⌋₊)
    (hupper : discreteDistance g ⌈(1 + b) * T⌉₊ ≤ ε) :
    (mixingTime g ε : ℝ) / (mixingTime g (1 - ε) : ℝ) ≤
      (1 + b) / (1 - b) + 1 / ((1 - b) * T) := by
  have hlo := lt_mixingTime_of_lt_distance g (sub_pos.mpr hε1) hlower
  have hup := (mixingTime_le_iff g hε0 _).mpr hupper
  have htlo : (1 - b) * T < (mixingTime g (1 - ε) : ℝ) := by
    have hcast : (⌊(1 - b) * T⌋₊ : ℝ) + 1 ≤ (mixingTime g (1 - ε) : ℝ) := by
      exact_mod_cast hlo
    exact (Nat.lt_floor_add_one _).trans_le hcast
  have hthi : (mixingTime g ε : ℝ) ≤ (1 + b) * T + 1 := by
    have hcast : (mixingTime g ε : ℝ) ≤ (⌈(1 + b) * T⌉₊ : ℝ) := by
      exact_mod_cast hup
    exact hcast.trans (Nat.ceil_lt_add_one (by positivity)).le
  have htpos : 0 < (1 - b) * T := mul_pos (sub_pos.mpr hb1) hT
  have hden : 0 < (mixingTime g (1 - ε) : ℝ) := htpos.trans htlo
  calc
    (mixingTime g ε : ℝ) / (mixingTime g (1 - ε) : ℝ) ≤
        ((1 + b) * T + 1) / (mixingTime g (1 - ε) : ℝ) :=
      div_le_div_of_nonneg_right hthi hden.le
    _ ≤ ((1 + b) * T + 1) / ((1 - b) * T) :=
      div_le_div_of_nonneg_left (by positivity) htpos htlo.le
    _ = (1 + b) / (1 - b) + 1 / ((1 - b) * T) := by
      field_simp

end MixingTime

section Measurability
variable {n : ℕ}

@[fun_prop] theorem measurable_mixingTime {ε : ℝ} (hε : 0 < ε) :
    Measurable (fun g : Disorder n => mixingTime g ε) := by
  apply measurable_of_Iic
  intro k
  have heq : (fun g : Disorder n => mixingTime g ε) ⁻¹' Set.Iic k =
      {g : Disorder n | discreteDistance g k ≤ ε} := by
    ext g
    exact mixingTime_le_iff g hε k
  rw [heq]
  exact measurableSet_le (continuous_discreteDistance k).measurable measurable_const

end Measurability

end SKRatio

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Dynamics_Median
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology _root_.OAI.SKRatioGaussian.instNonemptyUnitBall
attribute [-simp] _root_.OAI.SKRatio.Calculus.field_reversal _root_.OAI.SKRatio.Calculus.gibbsEuclideanEquiv_apply _root_.OAI.SKRatio.Calculus.lift_scalarEigenfunction _root_.OAI.SKRatio.Calculus.mass_reversal _root_.OAI.SKRatio.Calculus.reversal_reversal _root_.OAI.SKRatio.Calculus.spin_reversal _root_.OAI.SKRatio.Calculus.stationaryPairingCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap MeasureTheory Filter
namespace SKRatio.Calculus

lemma continuousKernel_continuous_time {n : ℕ} (J : Interaction n) (x y : Spin n) :
    Continuous (fun t : ℝ => continuousKernel J t x y) := by
  unfold continuousKernel
  exact (continuous_apply x).comp ((semigroup_continuous J).clm_apply continuous_const)

lemma continuousDistance_continuous_time {n : ℕ} (g : Disorder n) :
    Continuous (continuousDistance g) := by
  have h : Continuous (Finset.univ.sup' Finset.univ_nonempty
      (fun (x : Spin n) (t : ℝ) =>
        totalVariation (continuousKernel (coupling g) t x) (mass g 0))) := by
    apply Continuous.finset_sup'
    intro x _
    unfold totalVariation
    apply continuous_const.mul
    exact continuous_finsetSum _ (fun y _ =>
      ((continuousKernel_continuous_time _ x y).sub continuous_const).abs)
  exact h.congr (fun t => Finset.sup'_apply _ _ t)

lemma continuousKernel_pos {n : ℕ} (g : Disorder n) {t : ℝ} (ht : 0 < t)
    (x y : Spin n) : 0 < continuousKernel (coupling g) t x y := by
  by_cases hn : n = 0
  · subst n
    have h := continuousKernel_sum (coupling g) t x
    rw [Fintype.sum_subsingleton _ y] at h
    linarith only [h]
  · have hn' : 0 < n := Nat.pos_of_ne_zero hn
    have hs := continuousKernel_poisson_hasSum hn' g t x y
    have hpos : 0 < Real.exp (-(n:ℝ)*t) * ((n:ℝ)*t)^n /
        (n.factorial:ℝ) * (transition g^n) x y := by
      exact mul_pos (div_pos (mul_pos (Real.exp_pos _) (pow_pos
        (mul_pos (Nat.cast_pos.mpr hn') ht) _)) (Nat.cast_pos.mpr (Nat.factorial_pos _)))
        (transition_n_pos g x y)
    exact hpos.trans_le (hs.tsum_eq ▸ hs.summable.le_tsum n (fun k _ => by
      exact mul_nonneg (div_nonneg (mul_nonneg (Real.exp_nonneg _)
        (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) ht.le) _)) (Nat.cast_nonneg _))
        ((transition_pow_stochastic g k).1 x y)))

lemma continuousKernel_nat {n : ℕ} (J : Interaction n) (k : ℕ) :
    continuousKernel J (k : ℝ) = (continuousKernel J 1)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one, continuousKernel_add, ih, pow_succ]

lemma exists_continuous_geometric_bound {n : ℕ} (g : Disorder n) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ k : ℕ, continuousDistance g k ≤ r^k := by
  obtain ⟨r, hr0, hr1, hr⟩ := exists_geometric_block_bound
    (continuousKernel (coupling g) 1) (continuousKernel_stochastic _ (by norm_num))
    (mass g 0) (mass_nonneg g 0) (sum_mass g 0) 1
    (by simpa only [pow_one] using continuousKernel_pos g (by norm_num : (0:ℝ)<1))
    (by simpa only [pow_one] using continuousKernel_stationary g 1)
  refine ⟨r, hr0, hr1, fun k => ?_⟩
  unfold continuousDistance
  rw [continuousKernel_nat]
  apply Finset.sup'_le
  intro x _
  simpa only [one_mul] using hr k x

lemma exists_continuous_mixing_time {n : ℕ} (g : Disorder n) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 ≤ t ∧ continuousDistance g t ≤ ε := by
  obtain ⟨r, hr0, hr1, hbound⟩ := exists_continuous_geometric_bound g
  obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).eventually
    (gt_mem_nhds hε)).exists
  exact ⟨k, Nat.cast_nonneg _, (hbound k).trans hk.le⟩

lemma medianTime_mem {n : ℕ} (g : Disorder n) :
    0 ≤ medianTime g ∧ continuousDistance g (medianTime g) ≤ 1/2 := by
  apply IsClosed.csInf_mem
    ((isClosed_le continuous_const continuous_id).inter
      (isClosed_le (continuousDistance_continuous_time g) continuous_const))
    (exists_continuous_mixing_time g (by norm_num))
    ⟨0, fun _ ht => ht.1⟩

lemma medianTime_le_iff {n : ℕ} (g : Disorder n) {t : ℝ} (ht : 0 ≤ t) :
    medianTime g ≤ t ↔ continuousDistance g t ≤ 1/2 := by
  constructor
  · intro h
    exact (continuousDistance_antitone g (medianTime_mem g).1 h).trans (medianTime_mem g).2
  · intro h
    exact csInf_le ⟨0, fun _ h => h.1⟩ ⟨ht, h⟩

lemma before_median {n : ℕ} (g : Disorder n) {t : ℝ} (ht : 0 ≤ t)
    (hbefore : t < medianTime g) : 1/2 < continuousDistance g t := by
  exact lt_of_not_ge (fun h => not_le_of_gt hbefore ((medianTime_le_iff g ht).mpr h))

lemma median_cutoff_sides_of_lag {n : ℕ} (g : Disorder n)
    {c C b δ : ℝ} (hc : 0 < c) (hb : 0 < b) (hb' : b < 1)
    (hδ : δ < 1/2) (hn : 1 < n)
    (hscale : c * Real.log n ≤ medianTime g ∧ medianTime g ≤ C * Real.log n)
    (hlag : ∀ t : ℝ, 0 ≤ t →
      t + (b*c/2)*Real.log n ≤ ((1+b)*C)*Real.log n →
      continuousDistance g t ≤ 1-δ →
      continuousDistance g (t+(b*c/2)*Real.log n) ≤ δ) :
    1-δ < continuousDistance g ((1-b)*medianTime g) ∧
      continuousDistance g ((1+b)*medianTime g) ≤ δ := by
  let s : ℝ := (b*c/2)*Real.log n
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hs : 0 < s := by dsimp [s]; positivity
  have hm : 0 ≤ medianTime g := (medianTime_mem g).1
  have hsmed : s ≤ b*medianTime g/2 := by
    have h := mul_le_mul_of_nonneg_left hscale.1 (div_nonneg hb.le (by norm_num : (0:ℝ)≤2))
    dsimp [s]
    nlinarith only [h]
  have hshift : medianTime g+s ≤ (1+b)*medianTime g := by nlinarith only [hsmed, hs]
  have hhor : medianTime g+s ≤ ((1+b)*C)*Real.log n := by
    calc
      _ ≤ (1+b)*medianTime g := hshift
      _ ≤ (1+b)*(C*Real.log n) :=
        mul_le_mul_of_nonneg_left hscale.2 (by linarith)
      _ = _ := by ring
  have hlo : 0 ≤ (1-b)*medianTime g := mul_nonneg (by linarith) hm
  have hlobefore : (1-b)*medianTime g+s < medianTime g := by
    nlinarith only [hsmed, hs]
  constructor
  · by_contra h
    have ht := hlag ((1-b)*medianTime g) hlo
      ((le_of_lt hlobefore).trans ((le_add_of_nonneg_right hs.le).trans hhor))
      (le_of_not_gt h)
    have hbefore := before_median g (add_nonneg hlo hs.le) hlobefore
    exact not_lt_of_ge (ht.trans hδ.le) hbefore
  · have hcmed : continuousDistance g (medianTime g) ≤ 1-δ := by
      linarith only [(medianTime_mem g).2, hδ]
    exact (continuousDistance_antitone g (add_nonneg hm hs.le) hshift).trans
      (hlag (medianTime g) hm hhor hcmed)

lemma uniform_continuous_cutoff_of_positive_lag
    (G : ∀ n : ℕ, Set (Disorder n)) {c C : ℝ} (hc : 0 < c)
    (hscale : ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      c*Real.log n ≤ medianTime g ∧ medianTime g ≤ C*Real.log n)
    (hlag : ∀ ε α D δ : ℝ, 0 < ε → 0 < α → 0 < δ →
      ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ t : ℝ,
      0 ≤ t → t+α*Real.log n ≤ D*Real.log n →
      continuousDistance g t ≤ 1-ε → continuousDistance g (t+α*Real.log n) ≤ δ)
    {b : ℝ} (hb : 0 < b) (hb' : b < 1) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      1-δ < continuousDistance g ((1-b)*medianTime g) ∧
        continuousDistance g ((1+b)*medianTime g) ≤ δ := by
  let e : ℝ := min δ (1/4)
  have he : 0 < e := lt_min hδ (by norm_num)
  have heδ : e ≤ δ := min_le_left _ _
  have hehalf : e < 1/2 := (min_le_right _ _).trans_lt (by norm_num)
  have ha : 0 < b*c/2 := by positivity
  filter_upwards [hscale, hlag e (b*c/2) ((1+b)*C) e he ha he,
    eventually_gt_atTop 1] with n hnscale hnlag hn
  intro g hg
  obtain ⟨hl, hu⟩ := median_cutoff_sides_of_lag g hc hb hb' hehalf hn
    (hnscale g hg) (hnlag g hg)
  exact ⟨(by linarith only [heδ, hl]), hu.trans heδ⟩

end SKRatio.Calculus

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_SpectralLower
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology _root_.OAI.SKRatioGaussian.instNonemptyUnitBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap MeasureTheory Filter

namespace SKRatio.Calculus
attribute [local instance] Classical.propDecidable

lemma stationaryInner_symm {n : ℕ} (g : Disorder n) (f h : Observables n) :
    stationaryInner g f h = stationaryInner g h f := by
  simp only [stationaryInner, mul_comm (f _) (h _)]

lemma stationaryInner_pow_symm {n : ℕ} (g : Disorder n)
    (A : Observables n →L[ℝ] Observables n)
    (hA : ∀ f h, stationaryInner g f (A h) = stationaryInner g (A f) h)
    (k : ℕ) (f h : Observables n) :
    stationaryInner g f ((A^k) h) = stationaryInner g ((A^k) f) h := by
  induction k generalizing f h with
  | zero => simp
  | succ k ih =>
    calc
      _ = stationaryInner g (A f) ((A^k) h) := by
        rw [pow_succ', mul_apply_eq_comp, hA]
      _ = stationaryInner g ((A^k) (A f)) h := ih (A f) h
      _ = _ := by rw [pow_succ, mul_apply_eq_comp]

lemma stationaryInner_exp_symm {n : ℕ} (g : Disorder n)
    (A : Observables n →L[ℝ] Observables n)
    (hA : ∀ f h, stationaryInner g f (A h) = stationaryInner g (A f) h)
    (f h : Observables n) :
    stationaryInner g f (NormedSpace.exp A h) = stationaryInner g (NormedSpace.exp A f) h := by
  have hf : HasSum (fun k : ℕ => ((k.factorial:ℝ)⁻¹)*stationaryInner g f ((A^k) h))
      (stationaryInner g f (NormedSpace.exp A h)) := by
    simpa only [map_smul,smul_eq_mul,stationaryPairingCLM_apply] using
      (stationaryPairingCLM g f).hasSum (exp_apply_hasSum A h)
  have hh : HasSum (fun k : ℕ => ((k.factorial:ℝ)⁻¹)*stationaryInner g h ((A^k) f))
      (stationaryInner g h (NormedSpace.exp A f)) := by
    simpa only [map_smul,smul_eq_mul,stationaryPairingCLM_apply] using
      (stationaryPairingCLM g h).hasSum (exp_apply_hasSum A f)
  have hp (k : ℕ) : stationaryInner g f ((A^k) h) = stationaryInner g h ((A^k) f) := by
    rw [stationaryInner_pow_symm g A hA,stationaryInner_symm]
  simp_rw [hp] at hf
  rw [← stationaryInner_symm g h]
  exact hf.unique hh

lemma semigroup_symmetric {n : ℕ} (g : Disorder n) (t : ℝ) (f h : Observables n) :
    stationaryInner g f (semigroup (coupling g) t h) =
      stationaryInner g (semigroup (coupling g) t f) h := by
  apply stationaryInner_exp_symm
  intro a b
  have he := congrArg (fun z : ℝ => t*z) (generator_symmetric g a b)
  change (∑ x, mass g 0 x*(a x*(t*generator (coupling g) b x))) =
    ∑ x, mass g 0 x*((t*generator (coupling g) a x)*b x)
  convert he using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [stationaryInner,FiniteLaw.mean,Finset.mul_sum] <;> apply Finset.sum_congr rfl <;> intro x _ <;> ring)

lemma exp_apply_of_eigenvector {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (A : E →L[ℝ] E) (f : E) (a : ℝ)
    (h : A f = a • f) : NormedSpace.exp A f = Real.exp a • f := by
  have hp (k : ℕ) : (A^k) f = a^k • f := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ',mul_apply_eq_comp,ih,map_smul,h,smul_smul,pow_succ]
  have hs : HasSum (fun k : ℕ => (k.factorial:ℝ)⁻¹*a^k) (Real.exp a) := by
    simpa only [smul_eq_mul,Real.exp_eq_exp_ℝ] using
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) a)
  apply (exp_apply_hasSum A f).unique
  simpa only [hp,smul_smul] using hs.smul_const f

lemma spectral_parseval {n : ℕ} (g : Disorder n) (f h : Observables n) :
    (∑ a, spectralCoefficient g f a*spectralCoefficient g h a) = stationaryInner g f h := by
  have he := (spinEigenbasis g).repr.inner_map_map (gibbsEuclideanEquiv g f) (gibbsEuclideanEquiv g h)
  rw [PiLp.inner_apply,gibbsEuclideanEquiv_inner] at he
  simpa only [spectralCoefficient,RCLike.inner_apply,conj_trivial,mul_comm] using he

lemma spectral_generator_coordinates {n : ℕ} (g : Disorder n) (f : Observables n)
    (a : Fin (Fintype.card (Spin n))) :
    spectralCoefficient g (-generator (coupling g) f) a = spinEigenvalues g a*spectralCoefficient g f a := by
  unfold spectralCoefficient
  rw [← negativeGeneratorEuclidean_lift]
  exact (negativeGeneratorEuclidean_symmetric g).eigenvectorBasis_apply_self_apply
    finrank_euclideanSpace (gibbsEuclideanEquiv g f) a

lemma generator_scalarEigenfunction {n : ℕ} (g : Disorder n) (a : Fin (Fintype.card (Spin n))) :
    generator (coupling g) (scalarEigenfunction g a) = -spinEigenvalues g a • scalarEigenfunction g a := by
  have he : negativeGeneratorEuclidean g (spinEigenbasis g a) = spinEigenvalues g a • spinEigenbasis g a :=
    (negativeGeneratorEuclidean_symmetric g).apply_eigenvectorBasis finrank_euclideanSpace a
  have hf : -generator (coupling g) (scalarEigenfunction g a) = spinEigenvalues g a • scalarEigenfunction g a := by
    apply (gibbsEuclideanEquiv g).injective
    rw [← negativeGeneratorEuclidean_lift,map_smul,lift_scalarEigenfunction]
    exact he
  simpa only [neg_neg,neg_smul] using congrArg Neg.neg hf

lemma semigroup_scalarEigenfunction {n : ℕ} (g : Disorder n) (a : Fin (Fintype.card (Spin n))) (t : ℝ) :
    semigroup (coupling g) t (scalarEigenfunction g a) =
      Real.exp (-spinEigenvalues g a*t) • scalarEigenfunction g a := by
  apply exp_apply_of_eigenvector
  rw [smul_apply]
  change t • generator (coupling g) (scalarEigenfunction g a) = _
  rw [generator_scalarEigenfunction,smul_smul,mul_comm]

lemma spectral_coordinates_inner {n : ℕ} (g : Disorder n) (f : Observables n)
    (a : Fin (Fintype.card (Spin n))) :
    spectralCoefficient g f a = stationaryInner g (scalarEigenfunction g a) f := by
  rw [spectralCoefficient,OrthonormalBasis.repr_apply_apply,← lift_scalarEigenfunction g a,
    gibbsEuclideanEquiv_inner]

lemma spectral_semigroup_coordinates {n : ℕ} (g : Disorder n) (f : Observables n) (t : ℝ)
    (a : Fin (Fintype.card (Spin n))) :
    spectralCoefficient g (semigroup (coupling g) t f) a =
      Real.exp (-spinEigenvalues g a*t)*spectralCoefficient g f a := by
  rw [spectral_coordinates_inner,spectral_coordinates_inner,semigroup_symmetric,semigroup_scalarEigenfunction]
  simp only [stationaryInner,FiniteLaw.mean,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma stationary_correlation_lower {n : ℕ} (g : Disorder n) (f : Observables n)
    (hnorm : stationaryInner g f f = 1) (t : ℝ) :
    Real.exp (-t*stationaryEnergy g f) ≤ stationaryInner g f (semigroup (coupling g) t f) := by
  have hsum : (∑ a, spectralCoefficient g f a^2) = 1 := by
    simpa only [pow_two,hnorm] using spectral_parseval g f f
  have hE : (∑ a, spectralCoefficient g f a^2*spinEigenvalues g a) = stationaryEnergy g f := by
    have he := spectral_parseval g f (-generator (coupling g) f)
    simp only [spectral_generator_coordinates] at he
    rw [stationaryEnergy_eq]
    change _ = -(∑ x, mass g 0 x * (f x * generator (coupling g) f x))
    have hinner : stationaryInner g f (-generator (coupling g) f) =
        -(∑ x, mass g 0 x * (f x * generator (coupling g) f x)) := by
      simp [stationaryInner,FiniteLaw.mean]
    rw [← hinner,← he]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have he := convexOn_exp.map_sum_le (s := Set.univ) (p := fun a => -t*spinEigenvalues g a)
    (fun a (_ : a ∈ Finset.univ) => sq_nonneg (spectralCoefficient g f a)) hsum (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul] at he
  have hl : (∑ a, spectralCoefficient g f a^2*(-t*spinEigenvalues g a)) = -t*stationaryEnergy g f := by
    rw [← hE,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hl] at he
  rw [← spectral_parseval]
  simp_rw [spectral_semigroup_coordinates]
  calc
    _ ≤ ∑ a, spectralCoefficient g f a ^ 2 * Real.exp (-t * spinEigenvalues g a) := he
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [show -spinEigenvalues g a * t = -t * spinEigenvalues g a by ring]
      ring

lemma gibbsMean_siteKernel {n : ℕ} (g : Disorder n) (i : Fin n) (f : Observables n) :
    FiniteLaw.mean (mass g 0) (fun x => ∑ y, siteKernel g i x y * f y) =
      FiniteLaw.mean (mass g 0) f := by
  unfold FiniteLaw.mean
  simp only [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, siteKernel_stationary]

lemma gibbsMean_spin_times_mean {n : ℕ} (g : Disorder n) (i : Fin n) :
    FiniteLaw.mean (mass g 0) (fun x => spin x i * mean (coupling g) x i) =
      FiniteLaw.mean (mass g 0) (fun x => mean (coupling g) x i ^ 2) := by
  have hpoint (x : Spin n) : (∑ y, siteKernel g i x y *
      (spin y i * mean (coupling g) y i)) = mean (coupling g) x i ^ 2 := by
    rw [siteKernel_apply, spin_flip_self]
    have hm : mean (coupling g) (flip i x) i = mean (coupling g) x i := by
      simp only [mean, field_flip _ (coupling_diag g)]
    rw [hm, flipRate]
    nlinarith only [congrArg (fun a : ℝ => a * mean (coupling g) x i ^ 2) (spin_sq x i)]
  rw [← gibbsMean_siteKernel g i, show
    (fun x => ∑ y, siteKernel g i x y * (spin y i * mean (coupling g) y i)) =
      (fun x => mean (coupling g) x i ^ 2) by funext x; exact hpoint x]

lemma stationary_weight_le_one {n : ℕ} (g : Disorder n) (i : Fin n) :
    FiniteLaw.mean (mass g 0) (fun x => gradientWeight (coupling g) x i) ≤ 1 := by
  have he : FiniteLaw.mean (mass g 0) (fun x => gradientWeight (coupling g) x i) =
      1 - FiniteLaw.mean (mass g 0) (fun x => mean (coupling g) x i ^ 2) := by
    simp only [gradientWeight, FiniteLaw.mean, mul_sub, mul_one, Finset.sum_sub_distrib,
      sum_mass]
    congr 1
    exact gibbsMean_spin_times_mean g i
  rw [he]
  have hn : 0 ≤ FiniteLaw.mean (mass g 0) (fun x => mean (coupling g) x i ^ 2) :=
    Finset.sum_nonneg (fun x _ => mul_nonneg (mass_nonneg g 0 x) (sq_nonneg _))
  linarith only [hn]

lemma stationaryEnergy_spin_le_one {n : ℕ} (g : Disorder n) (i : Fin n) :
    stationaryEnergy g (fun x => spin x i) ≤ 1 := by
  have hw (x : Spin n) : weightedGradient (coupling g) (fun y => spin y i) x =
      gradientWeight (coupling g) x i := by
    simp only [weightedGradient, halfDiff_spin, ite_pow, one_pow, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_ite, mul_one, mul_zero,
      Fintype.sum_ite_eq']
  unfold stationaryEnergy FiniteLaw.mean
  simp_rw [hw]
  exact stationary_weight_le_one g i

lemma spin_correlation_lower {n : ℕ} (g : Disorder n) (i : Fin n) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-t) ≤ stationaryInner g (fun x => spin x i)
      (semigroup (coupling g) t (fun x => spin x i)) := by
  have hnorm : stationaryInner g (fun x => spin x i) (fun x => spin x i) = 1 := by
    simp [stationaryInner, FiniteLaw.mean, ← pow_two, spin_sq, sum_mass]
  have hh := stationary_correlation_lower g (fun x => spin x i) hnorm t
  have hE := mul_le_mul_of_nonneg_left (stationaryEnergy_spin_le_one g i) ht
  exact (Real.exp_le_exp.mpr (by linarith only [hE])).trans hh

lemma halfDiff_linearObservable {n : ℕ} (a : Fin n → ℝ) (i : Fin n) (x : Spin n) :
    halfDiff i (linearObservable a) x = a i := by
  unfold linearObservable
  rw [halfDiff_sum]
  have he (j : Fin n) : halfDiff i (fun y => a j * spin y j) x = a j * halfDiff i (fun y => spin y j) x := by
    unfold halfDiff
    ring
  simp only [he, halfDiff_spin, mul_ite, mul_one, mul_zero, Fintype.sum_ite_eq]

lemma unweightedGradient_linearObservable {n : ℕ} (a : Fin n → ℝ) (x : Spin n) :
    unweightedGradient (linearObservable a) x = ∑ i, a i ^ 2 := by
  simp only [unweightedGradient, halfDiff_linearObservable]

lemma gibbsMean_linearObservable_zero {n : ℕ} (g : Disorder n) (a : Fin n → ℝ) :
    FiniteLaw.mean (mass g 0) (linearObservable a) = 0 := by
  let e : Spin n ≃ Spin n := Function.Involutive.toPerm reversal (fun x => reversal_reversal x)
  have he := Equiv.sum_comp e (fun x => mass g 0 x * linearObservable a x)
  change (∑ x, mass g 0 (reversal x) * linearObservable a (reversal x)) = _ at he
  have hr (x : Spin n) : linearObservable a (reversal x) = -linearObservable a x := by
    simp [linearObservable, spin_reversal, Finset.sum_neg_distrib]
  simp only [mass_reversal, hr, mul_neg, Finset.sum_neg_distrib] at he
  unfold FiniteLaw.mean
  linarith only [he]

lemma stationaryEnergy_linearObservable_le {n : ℕ} (g : Disorder n) (a : Fin n → ℝ) :
    stationaryEnergy g (linearObservable a) ≤ ∑ i, a i ^ 2 := by
  unfold stationaryEnergy FiniteLaw.mean weightedGradient
  simp only [halfDiff_linearObservable, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  have h := mul_le_mul_of_nonneg_right (stationary_weight_le_one g i) (sq_nonneg (a i))
  simpa only [FiniteLaw.mean, one_mul, Finset.sum_mul, mul_assoc] using h

lemma stationary_linearObservable_variance_le {n : ℕ} (g : Disorder n) {γ : ℝ}
    (hγ : 0 < γ)
    (hgap : ∀ f : Observables n, γ * FiniteLaw.variance (mass g 0) f ≤ stationaryEnergy g f)
    (a : Fin n → ℝ) :
    FiniteLaw.variance (mass g 0) (linearObservable a) ≤ (∑ i, a i ^ 2) / γ := by
  apply (le_div_iff₀ hγ).mpr
  simpa only [mul_comm γ] using (hgap (linearObservable a)).trans (stationaryEnergy_linearObservable_le g a)

lemma semigroup_linearObservable {n : ℕ} (J : Interaction n) (a : Fin n → ℝ) (t : ℝ) (x : Spin n) :
    semigroup J t (linearObservable a) x = ∑ i, a i * semigroup J t (fun y => spin y i) x := by
  have he : linearObservable a = ∑ i, a i • (fun y : Spin n => spin y i) := by
    ext y
    simp [linearObservable]
  rw [he, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

lemma exists_distinguishing_linear {n : ℕ} (hn : 0 < n) (g : Disorder n) {t : ℝ} (ht : 0 ≤ t) :
    ∃ x : Spin n, ∃ a : Fin n → ℝ, (∑ i, a i ^ 2) = 1 ∧
      Real.sqrt n * Real.exp (-t) ≤ semigroup (coupling g) t (linearObservable a) x := by
  let F (x : Spin n) := ∑ i, spin x i * semigroup (coupling g) t (fun y => spin y i) x
  have hsum : (n : ℝ) * Real.exp (-t) ≤ FiniteLaw.mean (mass g 0) F := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => spin_correlation_lower g i ht)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      stationaryInner, FiniteLaw.mean] at h
    unfold FiniteLaw.mean
    dsimp only [F]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact h
  obtain ⟨x, _, hmax⟩ := Finset.exists_max_image Finset.univ F Finset.univ_nonempty
  have hx : (n : ℝ) * Real.exp (-t) ≤ F x := by
    calc
      _ ≤ _ := hsum
      _ ≤ ∑ y, mass g 0 y * F x := Finset.sum_le_sum (fun y _ =>
        mul_le_mul_of_nonneg_left (hmax y (Finset.mem_univ y)) (mass_nonneg g 0 y))
      _ = _ := by rw [← Finset.sum_mul, sum_mass, one_mul]
  let a (i : Fin n) := spin x i / Real.sqrt n
  have hnp : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 hnp
  refine ⟨x, a, ?_, ?_⟩
  · simp only [a, div_pow, spin_sq, Real.sq_sqrt hnp.le, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  · rw [semigroup_linearObservable]
    have he : (∑ i, a i * semigroup (coupling g) t (fun y => spin y i) x) = F x / Real.sqrt n := by
      simp only [a, F, Finset.sum_div, div_mul_eq_mul_div]
    rw [he]
    apply (le_div_iff₀ hsqrt).mpr
    have heq : Real.sqrt n * Real.exp (-t) * Real.sqrt n = (n : ℝ) * Real.exp (-t) := by
      nlinarith only [congrArg (fun z : ℝ => z * Real.exp (-t)) (Real.sq_sqrt hnp.le)]
    rwa [heq]

lemma continuousDistance_lower_of_linear_variances {n : ℕ} (hn : 0 < n)
    (g : Disorder n) {t V W : ℝ} (ht : 0 ≤ t)
    (htrans : ∀ (a : Fin n → ℝ), (∑ i, a i ^ 2) = 1 → ∀ x,
      FiniteLaw.variance (continuousKernel (coupling g) t x) (linearObservable a) ≤ V)
    (hstat : ∀ (a : Fin n → ℝ), (∑ i, a i ^ 2) = 1 →
      FiniteLaw.variance (mass g 0) (linearObservable a) ≤ W) :
    1 - 2*(V+W)*Real.exp (2*t)/n ≤ continuousDistance g t := by
  obtain ⟨x,a,ha,hm⟩ := exists_distinguishing_linear hn g ht
  let m := semigroup (coupling g) t (linearObservable a) x
  let d := totalVariation (continuousKernel (coupling g) t x) (mass g 0)
  have hcommon := FiniteLaw.common_mass_square (continuousKernel (coupling g) t x)
    (mass g 0) (linearObservable a) (continuousKernel_nonneg _ t ht x)
    (mass_nonneg g 0) (continuousKernel_sum _ t x) (sum_mass g 0)
  rw [gibbsMean_linearObservable_zero, sub_zero, ← semigroup_eq_kernel] at hcommon
  have hm0 : 0 ≤ m := by
    dsimp [m]
    exact (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_nonneg _)).trans hm
  have hsq : (n : ℝ)*Real.exp (-2*t) ≤ m^2 := by
    have h := (sq_le_sq₀ (by positivity : 0 ≤ Real.sqrt n * Real.exp (-t)) hm0).mpr hm
    have he : (Real.exp (-t))^2 = Real.exp (-2*t) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), he] using h
  have hbound : (1-continuousDistance g t)*((n : ℝ)*Real.exp (-2*t)) ≤ 2*(V+W) := by
    calc
      _ ≤ (1-continuousDistance g t)*m^2 := mul_le_mul_of_nonneg_left hsq
        (sub_nonneg.mpr (continuousDistance_le_one g ht))
      _ ≤ (1-d)*m^2 := mul_le_mul_of_nonneg_right
        (sub_le_sub_left (tv_le_continuousDistance g t x) 1) (sq_nonneg m)
      _ ≤ 2*FiniteLaw.variance (continuousKernel (coupling g) t x) (linearObservable a) +
        2*FiniteLaw.variance (mass g 0) (linearObservable a) := hcommon
      _ ≤ 2*(V+W) := by linarith only [htrans a ha x, hstat a ha]
  have hnp : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have heq : ((n : ℝ)*Real.exp (-2*t)) * (Real.exp (2*t)/n) = 1 := by
    rw [mul_div_assoc', mul_assoc (n : ℝ), ← Real.exp_add,
      show -2*t+2*t=0 by ring, Real.exp_zero, mul_one, div_self hnp.ne']
  have hmultiply := mul_le_mul_of_nonneg_right hbound
    (div_nonneg (Real.exp_nonneg (2*t)) hnp.le)
  rw [mul_assoc, heq, mul_one] at hmultiply
  rw [← mul_div_assoc] at hmultiply
  linarith only [hmultiply]

lemma exp_quarter_log_div {n : ℕ} (hn : 0 < n) :
    Real.exp (2*(Real.log n/4))/(n : ℝ) = dimensionDecay (1/2) n := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have he : (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hn').symm
  conv_lhs => rhs; rw [he]
  rw [← Real.exp_sub]
  unfold dimensionDecay
  congr 1
  ring

theorem uniform_strong_lower_of_small_set
    (G : ∀ n : ℕ, Set (Disorder n))
    (bad : ∀ n, Disorder n → Set (Spin n)) {κ A d₀ γ : ℝ}
    (hκ : 0 < κ) (hA : 0 ≤ A) (hd₀ : 0 ≤ d₀) (hγ : 0 < γ)
    (hgap : ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ f : Observables n,
      γ*FiniteLaw.variance (mass g 0) f ≤ stationaryEnergy g f)
    (hdrift : ∀ D : ℝ, 0 < D → ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      ∀ (f : Observables n), ∀ r ∈ Set.Icc (0:ℝ) (D*Real.log n), ∀ y,
      deriv (fun v => unweightedGradient (semigroup (coupling g) v f) y) r -
        generator (coupling g) (unweightedGradient (semigroup (coupling g) r f)) y ≤
          (-κ + if y ∈ bad n g then A else 0)*
            unweightedGradient (semigroup (coupling g) r f) y)
    (havoid : ∀ D m : ℝ, 0 < D → 0 < m →
      ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ u ∈ Set.Icc d₀ (D*Real.log n), ∀ x,
      semigroup (coupling g) u (fun y => if y ∈ bad n g then 1 else 0) x ≤ dimensionDecay m n) :
    ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      1-2*(4*(Real.exp (A*d₀)/κ+1)+1/γ)*dimensionDecay (1/2) n ≤
        continuousDistance g (Real.log n/4) := by
  have hmom := uniform_gradient_moments_of_small_set G bad hκ hA hd₀ hdrift havoid
    (D := 1) (R := 1) (by norm_num) (by norm_num)
  filter_upwards [hgap, hmom, eventually_ge_atTop 1] with n hngap hnmom hn
  intro g hg
  have hn' : 0 < n := hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have htime : Real.log n/4 ∈ Set.Icc (0 : ℝ) (1*Real.log n) := by
    constructor <;> linarith only [hlog]
  have htrans (a : Fin n → ℝ) (ha : (∑ i, a i ^ 2) = 1) (x : Spin n) :
      FiniteLaw.variance (continuousKernel (coupling g) (Real.log n/4) x)
        (linearObservable a) ≤ 4*(Real.exp (A*d₀)/κ+1) := by
    simpa only [one_mul] using (hnmom g hg (linearObservable a)
      (fun y => by rw [unweightedGradient_linearObservable,ha]) (Real.log n/4) htime).1 x
  have hstat (a : Fin n → ℝ) (ha : (∑ i, a i ^ 2) = 1) :
      FiniteLaw.variance (mass g 0) (linearObservable a) ≤ 1/γ := by
    simpa only [ha] using stationary_linearObservable_variance_le g hγ (hngap g hg) a
  have h := continuousDistance_lower_of_linear_variances hn' g htime.1 htrans hstat
  rw [mul_div_assoc, exp_quarter_log_div hn'] at h
  exact h

theorem uniform_median_lower_of_small_set
    (G : ∀ n : ℕ, Set (Disorder n))
    (bad : ∀ n, Disorder n → Set (Spin n)) {κ A d₀ γ : ℝ}
    (hκ : 0 < κ) (hA : 0 ≤ A) (hd₀ : 0 ≤ d₀) (hγ : 0 < γ)
    (hgap : ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ f : Observables n,
      γ*FiniteLaw.variance (mass g 0) f ≤ stationaryEnergy g f)
    (hdrift : ∀ D : ℝ, 0 < D → ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      ∀ (f : Observables n), ∀ r ∈ Set.Icc (0:ℝ) (D*Real.log n), ∀ y,
      deriv (fun v => unweightedGradient (semigroup (coupling g) v f) y) r -
        generator (coupling g) (unweightedGradient (semigroup (coupling g) r f)) y ≤
          (-κ + if y ∈ bad n g then A else 0)*
            unweightedGradient (semigroup (coupling g) r f) y)
    (havoid : ∀ D m : ℝ, 0 < D → 0 < m →
      ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ u ∈ Set.Icc d₀ (D*Real.log n), ∀ x,
      semigroup (coupling g) u (fun y => if y ∈ bad n g then 1 else 0) x ≤ dimensionDecay m n) :
    ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, Real.log n/4 ≤ medianTime g := by
  have hlower := uniform_strong_lower_of_small_set G bad hκ hA hd₀ hγ hgap hdrift havoid
  have hdecay := (dimensionDecay_tendsto_zero (by norm_num : (0 : ℝ)<1/2)).const_mul
    (2*(4*(Real.exp (A*d₀)/κ+1)+1/γ))
  simp only [mul_zero] at hdecay
  filter_upwards [hlower, hdecay.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/2)),
    eventually_ge_atTop 1] with n hnlow hdec hn
  intro g hg
  have ht : 0 ≤ Real.log n/4 := div_nonneg
    (Real.log_nonneg (by exact_mod_cast hn)) (by norm_num)
  have hdist : 1/2 < continuousDistance g (Real.log n/4) := by
    linarith only [hnlow g hg,hdec]
  exact le_of_lt (lt_of_not_ge (fun h => not_lt_of_ge ((medianTime_le_iff g ht).mp h) hdist))

end SKRatio.Calculus

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Dynamics_LogQuadratic
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology _root_.OAI.SKRatioGaussian.instNonemptyUnitBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators

open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SKRatioClock.Clock

lemma logQuadratic_mul_sq (x : ℝ) :
    logQuadratic x*x^2 = Real.log (1+x)-x := by
  classical
  by_cases hx : x=0
  · subst x
    simp [logQuadratic]
  · simp only [logQuadratic, Function.update_of_ne hx]
    exact div_mul_cancel₀ _ (pow_ne_zero 2 hx)

lemma continuousAt_logQuadratic : ContinuousAt logQuadratic 0 := by
  classical
  apply continuousAt_update_same.mpr
  have hdom : ∀ᶠ x : ℝ in 𝓝[≠] 0, 0 < 1+x := by
    filter_upwards [(eventually_gt_nhds (by norm_num : (-1:ℝ)<0)).filter_mono nhdsWithin_le_nhds]
      with x hx
    linarith
  have hne : ∀ᶠ x : ℝ in 𝓝[≠] 0, x ≠ 0 := self_mem_nhdsWithin
  apply HasDerivAt.lhopital_zero_nhdsNE
    (f' := fun x => 1/(1+x)-1) (g' := fun x => 2*x)
  · filter_upwards [hdom] with x hx
    exact ((hasDerivAt_id x).const_add 1 |>.log hx.ne').sub (hasDerivAt_id x)
  · exact Filter.Eventually.of_forall fun x => by
      convert! (hasDerivAt_id x).mul (hasDerivAt_id x) using 1
      · ext t
        simp [pow_two]
      · simp [two_mul]
  · filter_upwards [hne] with x hx
    exact mul_ne_zero (by norm_num) hx
  · have h : Tendsto (fun x : ℝ => Real.log (1+x)-x) (𝓝 0) (𝓝 0) := by
      have hc : ContinuousAt (fun x : ℝ => Real.log (1+x)-x) 0 := by
        apply ContinuousAt.sub
        · apply ContinuousAt.log
          · fun_prop
          · norm_num
        · fun_prop
      simpa using hc.tendsto
    exact h.mono_left nhdsWithin_le_nhds
  · have hc : ContinuousAt (fun x : ℝ => x^2) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  · have ht : Tendsto (fun x : ℝ => -1/(2*(1+x))) (𝓝[≠] 0) (𝓝 (-(1/2:ℝ))) := by
      have hc : ContinuousAt (fun x : ℝ => -1/(2*(1+x))) 0 := by
        apply ContinuousAt.div <;> first | fun_prop | norm_num
      convert hc.tendsto.mono_left nhdsWithin_le_nhds using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
    apply ht.congr'
    filter_upwards [hne,hdom] with x hx hd
    field_simp
    ring

lemma poissonMass_stirling {m : ℝ} (hm : 0 < m) {k : ℕ} (hk : 0 < k) :
    Real.sqrt k*poissonMass m k =
      Real.exp ((k:ℝ)*(Real.log (m/k)-(m-k)/k))/
        (Real.sqrt 2*Stirling.stirlingSeq k) := by
  have hk0 : (k:ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hkp : (0:ℝ)<k := by exact_mod_cast hk
  have he : Real.exp ((k:ℝ)*(Real.log (m/k)-(m-k)/k)) =
      Real.exp (-m)*(m/(k/Real.exp 1))^k := by
    have ha : (k:ℝ)*(Real.log (m/k)-(m-k)/k) =
        -m+(k:ℝ)*(Real.log (m/k)+1) := by field_simp; ring
    rw [ha, Real.exp_add, Real.exp_nat_mul, Real.exp_add, Real.exp_log (div_pos hm hkp)]
    congr 2
    field_simp
  rw [he]
  unfold poissonMass Stirling.stirlingSeq
  rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
  have hs : Real.sqrt (k:ℝ) ≠ 0 := (Real.sqrt_pos.2 hkp).ne'
  have hs2 : Real.sqrt (2:ℝ) ≠ 0 := by positivity
  have hf : (k.factorial:ℝ) ≠ 0 := by positivity
  have hx : (k:ℝ)/Real.exp 1 ≠ 0 := div_ne_zero hk0 (Real.exp_ne_zero _)
  rw [div_pow]
  field_simp

theorem poisson_local_limit {k : ℕ → ℕ} {m : ℕ → ℝ} {z : ℝ}
    (hk : Tendsto k atTop atTop) (hm : ∀ᶠ n in atTop, 0 < m n)
    (hd : Tendsto (fun n => (m n-(k n:ℝ))/Real.sqrt (k n)) atTop (𝓝 z)) :
    Tendsto (fun n => Real.sqrt (k n)*poissonMass (m n) (k n)) atTop
      (𝓝 (Real.exp (-(z^2)/2)/(Real.sqrt 2*Real.sqrt Real.pi))) := by
  have hkn : Tendsto (fun n => (k n:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hk
  have hks : Tendsto (fun n => Real.sqrt (k n:ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hkn
  have hkpos : ∀ᶠ n in atTop, 0 < k n := hk.eventually (eventually_gt_atTop 0)
  have hh : Tendsto (fun n => (m n-(k n:ℝ))/(k n:ℝ)) atTop (𝓝 0) := by
    apply (hd.div_atTop hks).congr'
    filter_upwards [hkpos] with n hn
    have hn0 : (0:ℝ)≤k n := Nat.cast_nonneg _
    rw [div_div, Real.mul_self_sqrt hn0]
  have hq : Tendsto (fun n => logQuadratic ((m n-(k n:ℝ))/(k n:ℝ))) atTop
      (𝓝 (-(1/2:ℝ))) := by
    have h := continuousAt_logQuadratic.tendsto.comp hh
    simpa [Function.comp_def,logQuadratic] using h
  have hprod := hq.mul (hd.pow 2)
  have he : Tendsto (fun n => (k n:ℝ)*(Real.log (m n/k n)-(m n-k n)/k n))
      atTop (𝓝 (-(z^2)/2)) := by
    have ht : (-(1/2:ℝ))*z^2 = -(z^2)/2 := by ring
    rw [ht] at hprod
    apply hprod.congr'
    filter_upwards [hkpos] with n hn
    have hn0 : (k n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hsn : Real.sqrt (k n:ℝ)^2 = k n := Real.sq_sqrt (Nat.cast_nonneg _)
    have hlog : 1+(m n-(k n:ℝ))/(k n:ℝ) = m n/k n := by field_simp; ring
    have h := logQuadratic_mul_sq ((m n-(k n:ℝ))/(k n:ℝ))
    rw [hlog] at h
    rw [div_pow,hsn]
    calc
      _ = (k n:ℝ)*(logQuadratic ((m n-(k n:ℝ))/(k n:ℝ))*
        ((m n-(k n:ℝ))/(k n:ℝ))^2) := by field_simp
      _ = _ := by rw [h]
  have hdnom : Tendsto (fun n => Real.sqrt 2*Stirling.stirlingSeq (k n)) atTop
      (𝓝 (Real.sqrt 2*Real.sqrt Real.pi)) :=
    tendsto_const_nhds.mul (Stirling.tendsto_stirlingSeq_sqrt_pi.comp hk)
  have heexp := Real.continuous_exp.continuousAt.tendsto.comp he
  apply (heexp.div hdnom (by positivity)).congr'
  filter_upwards [hm,hkpos] with n hn hnk
  exact (poissonMass_stirling hn hnk).symm

lemma center_ratio_tendsto (q x : ℝ) :
    Tendsto (fun n : ℕ => (q*n+x*Real.sqrt n)/(n:ℝ)) atTop (𝓝 q) := by
  have hs := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have h : Tendsto (fun n : ℕ => q+x/Real.sqrt n) atTop (𝓝 q) := by
    simpa using (tendsto_const_nhds.add (tendsto_const_nhds.div_atTop hs))
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsn : Real.sqrt (n:ℝ) ≠ 0 := by positivity
  have hsq := Real.sq_sqrt (Nat.cast_nonneg n)
  field_simp
  nlinarith [congrArg (fun t => x*t) hsq]

lemma center_tendsto_atTop {q : ℝ} (hq : 0 < q) (x : ℝ) :
    Tendsto (fun n : ℕ => q*n+x*Real.sqrt n) atTop atTop := by
  have h := (center_ratio_tendsto q x).pos_mul_atTop hq
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact div_mul_cancel₀ _ (by exact_mod_cast hn.ne')

lemma centralIndex_atTop {q : ℝ} (hq : 0 < q) (x : ℝ) :
    Tendsto (centralIndex q x) atTop atTop :=
  tendsto_nat_floor_atTop.comp (center_tendsto_atTop hq x)

lemma centralIndex_deviation {q : ℝ} (hq : 0 < q) (x : ℝ) :
    Tendsto (fun n => ((centralIndex q x n:ℝ)-q*n)/Real.sqrt n) atTop (𝓝 x) := by
  have hs := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hzero : Tendsto (fun n : ℕ => 1/Real.sqrt n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hs
  have hneg : Tendsto (fun n : ℕ => -(1/Real.sqrt n)) atTop (𝓝 0) := by
    simpa using hzero.neg
  have he : Tendsto (fun n => ((centralIndex q x n:ℝ)-
      (q*n+x*Real.sqrt n))/Real.sqrt n) atTop (𝓝 0) := by
    apply hneg.squeeze' tendsto_const_nhds
    · filter_upwards [(center_tendsto_atTop hq x).eventually (eventually_ge_atTop 0),
        eventually_gt_atTop 0] with n hn hn0
      have hspos : 0 < Real.sqrt (n:ℝ) := by positivity
      have hh := Nat.lt_floor_add_one (q*n+x*Real.sqrt n)
      change -(1/Real.sqrt (n:ℝ)) ≤ _
      rw [← neg_div]
      apply div_le_div_of_nonneg_right _ hspos.le
      dsimp [centralIndex]
      linarith
    · filter_upwards [(center_tendsto_atTop hq x).eventually (eventually_ge_atTop 0)]
        with n hn
      apply div_nonpos_of_nonpos_of_nonneg _ (Real.sqrt_nonneg _)
      exact sub_nonpos.mpr (Nat.floor_le hn)
  have htt : Tendsto (fun n => (((centralIndex q x n:ℝ)-
      (q*n+x*Real.sqrt n))/Real.sqrt n)+x) atTop (𝓝 x) := by
    simpa using he.add_const x
  apply htt.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hsn : Real.sqrt (n:ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma centralIndex_ratio {q : ℝ} (hq : 0 < q) (x : ℝ) :
    Tendsto (fun n => (centralIndex q x n:ℝ)/(n:ℝ)) atTop (𝓝 q) := by
  have hs := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht : Tendsto (fun n => q+(((centralIndex q x n:ℝ)-q*n)/Real.sqrt n)/Real.sqrt n)
      atTop (𝓝 q) := by
    simpa using tendsto_const_nhds.add ((centralIndex_deviation hq x).div_atTop hs)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [div_div, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  field_simp
  ring

theorem poisson_scaled_local {q : ℝ} (hq : 0 < q) (x y : ℝ)
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (hkr : Tendsto (fun n => (k n:ℝ)/(n:ℝ)) atTop (𝓝 q))
    (hkd : Tendsto (fun n => ((k n:ℝ)-q*n)/Real.sqrt n) atTop (𝓝 x)) :
    Tendsto (fun n : ℕ => Real.sqrt (n:ℝ)*
      poissonMass (q*n+y*Real.sqrt n) (k n)) atTop
      (𝓝 (Real.exp (-((y-x)/Real.sqrt q)^2/2)/
        (Real.sqrt q*(Real.sqrt 2*Real.sqrt Real.pi)))) := by
  have hratio : Tendsto (fun n => Real.sqrt (k n:ℝ)/Real.sqrt n)
      atTop (𝓝 (Real.sqrt q)) := by
    have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hkr
    simpa only [Function.comp_def,Real.sqrt_div (Nat.cast_nonneg _)] using hh
  have hstd : Tendsto (fun n : ℕ => ((q*n+y*Real.sqrt n)-(k n:ℝ))/
      Real.sqrt (k n)) atTop (𝓝 ((y-x)/Real.sqrt q)) := by
    have hh := ((tendsto_const_nhds (x := y)).sub hkd).div hratio
      ((Real.sqrt_pos.2 hq).ne')
    apply hh.congr'
    filter_upwards [eventually_gt_atTop 0, hk.eventually (eventually_gt_atTop 0)]
      with n hn hk0
    have hsn : Real.sqrt (n:ℝ) ≠ 0 := by positivity
    have hsk : Real.sqrt (k n:ℝ) ≠ 0 := by positivity
    change (y-((k n:ℝ)-q*n)/Real.sqrt n)/
      (Real.sqrt (k n:ℝ)/Real.sqrt n) = _
    field_simp
    ring
  have hp := poisson_local_limit hk
    ((center_tendsto_atTop hq y).eventually (eventually_gt_atTop 0)) hstd
  have ht := hp.div hratio ((Real.sqrt_pos.2 hq).ne')
  have heconst : (Real.exp (-((y-x)/Real.sqrt q)^2/2)/
      (Real.sqrt 2*Real.sqrt Real.pi))/Real.sqrt q =
      Real.exp (-((y-x)/Real.sqrt q)^2/2)/
        (Real.sqrt q*(Real.sqrt 2*Real.sqrt Real.pi)) := by ring
  rw [heconst] at ht
  apply ht.congr'
  filter_upwards [hk.eventually (eventually_gt_atTop 0)] with n hn
  have hsk : Real.sqrt (k n:ℝ) ≠ 0 := by positivity
  change (Real.sqrt (k n:ℝ)*poissonMass _ _)/
    (Real.sqrt (k n:ℝ)/Real.sqrt n) = _
  field_simp

theorem poisson_histogram_pointwise {q : ℝ} (hq : 0 < q) (x y : ℝ) :
    Tendsto (fun n : ℕ => Real.sqrt (n:ℝ)*
      poissonMass (q*n+y*Real.sqrt n) (centralIndex q x n)) atTop
      (𝓝 (Real.exp (-((y-x)/Real.sqrt q)^2/2)/
        (Real.sqrt q*(Real.sqrt 2*Real.sqrt Real.pi)))) :=
  poisson_scaled_local hq x y (centralIndex q x) (centralIndex_atTop hq x)
    (centralIndex_ratio hq x) (centralIndex_deviation hq x)

lemma binomialMass_poisson {q : ℝ} {M k : ℕ} (hk : k ≤ M) (hM : 0 < M) :
    binomialMass q M k =
      poissonMass (q*M) k*poissonMass ((1-q)*M) (M-k)/poissonMass M M := by
  have hM0 : (M:ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  unfold binomialMass poissonMass
  rw [Nat.cast_choose ℝ hk]
  have he : Real.exp (-(q*(M:ℝ)))*Real.exp (-((1-q)*M)) = Real.exp (-(M:ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hp : (M:ℝ)^k*(M:ℝ)^(M-k) = (M:ℝ)^M := by
    rw [← pow_add, Nat.add_sub_of_le hk]
  simp only [mul_pow]
  have hf1 : (k.factorial:ℝ) ≠ 0 := by positivity
  have hf2 : ((M-k).factorial:ℝ) ≠ 0 := by positivity
  have hf3 : (M.factorial:ℝ) ≠ 0 := by positivity
  have he0 : Real.exp (-(M:ℝ)) ≠ 0 := Real.exp_ne_zero _
  field_simp
  calc
    _ = (M:ℝ)^M * Real.exp (-(M:ℝ)) *q^k*(1-q)^(M-k) := by ring
    _ = _ := by rw [← hp, ← he]; ring

lemma gaussian_formula {q : ℝ} (hq : 0 < q) (x y : ℝ) :
    Real.exp (-((y-x)/Real.sqrt q)^2/2)/
        (Real.sqrt q*(Real.sqrt 2*Real.sqrt Real.pi)) =
      gaussianPDFReal y ⟨q,hq.le⟩ x := by
  change _ = (Real.sqrt (2*Real.pi*q))⁻¹ * Real.exp (-(x-y)^2/(2*q))
  rw [Real.sqrt_mul (mul_nonneg (by norm_num) Real.pi_pos.le),
    Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
  have he : -((y-x)/Real.sqrt q)^2/2 = -(x-y)^2/(2*q) := by
    rw [div_pow, Real.sq_sqrt hq.le]
    ring
  rw [he]
  ring

lemma index_atTop_of_ratio {k : ℕ → ℕ} {q : ℝ} (hq : 0 < q)
    (hkr : Tendsto (fun n => (k n:ℝ)/(n:ℝ)) atTop (𝓝 q)) : Tendsto k atTop atTop := by
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  apply (hkr.pos_mul_atTop hq (tendsto_natCast_atTop_atTop (R := ℝ))).congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact div_mul_cancel₀ _ (by exact_mod_cast hn.ne')

lemma centralIndex_le {q : ℝ} (hql : 0 < q) (hqu : q < 1) (x : ℝ) :
    ∀ᶠ n in atTop, centralIndex q x n ≤ n := by
  filter_upwards [(centralIndex_ratio hql x).eventually (eventually_lt_nhds hqu),
    eventually_gt_atTop 0] with n hn hn0
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn0
  have hh := (div_lt_iff₀ hnpos).mp hn
  have hh' : (centralIndex q x n:ℝ) < n := by simpa using hh
  exact le_of_lt (by exact_mod_cast hh')

lemma complementIndex_ratio {q : ℝ} (hql : 0 < q) (hqu : q < 1) (x : ℝ) :
    Tendsto (fun n => ((n-centralIndex q x n:ℕ):ℝ)/(n:ℝ)) atTop (𝓝 (1-q)) := by
  apply ((tendsto_const_nhds (x := (1:ℝ))).sub (centralIndex_ratio hql x)).congr'
  filter_upwards [centralIndex_le hql hqu x,eventually_gt_atTop 0] with n hn hn0
  rw [Nat.cast_sub hn]
  have hne : (n:ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
  field_simp

lemma complementIndex_deviation {q : ℝ} (hql : 0 < q) (hqu : q < 1) (x : ℝ) :
    Tendsto (fun n => (((n-centralIndex q x n:ℕ):ℝ)-(1-q)*n)/Real.sqrt n)
      atTop (𝓝 (-x)) := by
  apply (centralIndex_deviation hql x).neg.congr'
  filter_upwards [centralIndex_le hql hqu x] with n hn
  rw [Nat.cast_sub hn]
  ring

lemma gaussian_product_quotient {q : ℝ} (hql : 0 < q) (hqu : q < 1) (x : ℝ) :
    gaussianPDFReal 0 ⟨q,hql.le⟩ x *
      gaussianPDFReal 0 ⟨1-q,by linarith⟩ (-x) /
      gaussianPDFReal 0 1 0 =
    gaussianPDFReal 0 ⟨q*(1-q),mul_nonneg hql.le (by linarith)⟩ x := by
  have hg1 : gaussianPDFReal 0 1 0 = 1/(Real.sqrt 2*Real.sqrt Real.pi) := by
    norm_num [gaussianPDFReal, Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
  rw [← gaussian_formula hql x 0, ← gaussian_formula (by linarith : 0 < 1-q) (-x) 0,
    hg1, ← gaussian_formula (mul_pos hql (by linarith : 0 < 1-q)) x 0]
  simp only [zero_sub, neg_div, neg_sq, neg_neg]
  have hq0 : q ≠ 0 := hql.ne'
  have hr0 : 1-q ≠ 0 := by linarith
  have he : -(x/Real.sqrt q)^2/2 + -(x/Real.sqrt (1-q))^2/2 =
      -(x/Real.sqrt (q*(1-q)))^2/2 := by
    simp only [div_pow, Real.sq_sqrt hql.le, Real.sq_sqrt (show 0≤1-q by linarith),
      Real.sq_sqrt (mul_nonneg hql.le (show 0≤1-q by linarith))]
    field_simp
    ring
  rw [mul_div_assoc, div_div, div_mul_div_comm]
  rw [← Real.exp_add]
  simp only [← neg_div]
  rw [he, Real.sqrt_mul hql.le]
  have hs : Real.sqrt q ≠ 0 := by positivity
  have hr : Real.sqrt (1-q) ≠ 0 := by positivity
  have h2 : Real.sqrt (2:ℝ) ≠ 0 := by positivity
  have hpi : Real.sqrt Real.pi ≠ 0 := by positivity
  field_simp

theorem binomial_histogram_pointwise {q : ℝ} (hql : 0 < q) (hqu : q < 1) (x : ℝ) :
    Tendsto (fun n : ℕ => Real.sqrt (n:ℝ)*binomialMass q n (centralIndex q x n)) atTop
      (𝓝 (gaussianPDFReal 0 ⟨q*(1-q),mul_nonneg hql.le (by linarith)⟩ x)) := by
  have ha := poisson_scaled_local hql x 0 (centralIndex q x) (centralIndex_atTop hql x)
    (centralIndex_ratio hql x) (centralIndex_deviation hql x)
  have hb := poisson_scaled_local (by linarith : 0 < 1-q) (-x) 0
    (fun n => n-centralIndex q x n)
    (index_atTop_of_ratio (by linarith) (complementIndex_ratio hql hqu x))
    (complementIndex_ratio hql hqu x) (complementIndex_deviation hql hqu x)
  have hc := poisson_scaled_local (by norm_num : (0:ℝ)<1) 0 0 (fun n => n) tendsto_id
    (by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop 0] with n hn
      exact (div_self (by exact_mod_cast hn.ne' : (n:ℝ) ≠ 0)).symm)
    (by simp)
  rw [gaussian_formula hql x 0] at ha
  rw [gaussian_formula (by linarith : 0 < 1-q) (-x) 0] at hb
  rw [gaussian_formula (by norm_num : (0:ℝ)<1) 0 0] at hc
  have hc1 : (⟨(1:ℝ),by norm_num⟩ : ℝ≥0) = 1 := by rfl
  rw [hc1] at hc
  have hh := (ha.mul hb).div hc (gaussianPDFReal_pos 0 1 0 (by norm_num)).ne'
  have heq : gaussianPDFReal 0 ⟨q,hql.le⟩ x *
      gaussianPDFReal 0 ⟨1-q,by linarith⟩ (-x) / gaussianPDFReal 0 1 0 =
      gaussianPDFReal 0 ⟨q*(1-q),mul_nonneg hql.le (by linarith)⟩ x :=
    gaussian_product_quotient hql hqu x
  have hh' : Tendsto (fun n : ℕ =>
      (Real.sqrt (n:ℝ)*poissonMass (q*n+0*Real.sqrt n) (centralIndex q x n))*
      (Real.sqrt (n:ℝ)*poissonMass ((1-q)*n+0*Real.sqrt n) (n-centralIndex q x n))/
      (Real.sqrt (n:ℝ)*poissonMass (1*n+0*Real.sqrt n) n)) atTop
      (𝓝 (gaussianPDFReal 0 ⟨q,hql.le⟩ x *
        gaussianPDFReal 0 ⟨1-q,by linarith⟩ (-x) / gaussianPDFReal 0 1 0)) := hh
  rw [heq] at hh'
  apply hh'.congr'
  filter_upwards [centralIndex_le hql hqu x,eventually_gt_atTop 0] with n hn hn0
  simp only [zero_mul,add_zero,one_mul]
  rw [binomialMass_poisson hn hn0]
  have hs : Real.sqrt (n:ℝ) ≠ 0 := by positivity
  field_simp

end SKRatioClock.Clock

open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Dynamics_ClockLower
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology _root_.OAI.SKRatioGaussian.instNonemptyUnitBall
attribute [-simp] _root_.OAI.SKRatio.Calculus.field_reversal _root_.OAI.SKRatio.Calculus.gibbsEuclideanEquiv_apply _root_.OAI.SKRatio.Calculus.lift_scalarEigenfunction _root_.OAI.SKRatio.Calculus.mass_reversal _root_.OAI.SKRatio.Calculus.reversal_reversal _root_.OAI.SKRatio.Calculus.spin_reversal _root_.OAI.SKRatio.Calculus.stationaryPairingCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory SKRatioClock
namespace SKRatio.Calculus

lemma poissonMass_nonneg {r : ℝ} (hr : 0 ≤ r) (j : ℕ) :
    0 ≤ Clock.poissonMass r j := by unfold Clock.poissonMass; positivity

lemma poissonMass_exp_hasSum (r s : ℝ) :
    HasSum (fun j => Clock.poissonMass r j*Real.exp (s*(j:ℝ)))
      (Real.exp (r*(Real.exp s-1))) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (r*Real.exp s)).mul_left (Real.exp (-r))
  convert! h using 1
  · funext j
    rw [mul_pow, ← Real.exp_nat_mul]
    unfold Clock.poissonMass
    ring_nf
  · rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add]
    congr 1
    ring

lemma poisson_head_le {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (k : ℕ) :
    (∑ j ∈ Finset.range k, Clock.poissonMass r j) ≤
      Real.exp (s*(k:ℝ)+r*(Real.exp (-s)-1)) := by
  have hsum := (poissonMass_exp_hasSum r (-s)).mul_left (Real.exp (s*k))
  have hle : (∑ j ∈ Finset.range k, Clock.poissonMass r j) ≤
      ∑ j ∈ Finset.range k, Real.exp (s*k)*(Clock.poissonMass r j*Real.exp (-s*j)) := by
    apply Finset.sum_le_sum
    intro j hj
    have hj' : (j:ℝ) ≤ k := by exact_mod_cast (Finset.mem_range.mp hj).le
    calc
      _ ≤ Clock.poissonMass r j * Real.exp (s*((k:ℝ)-j)) := by
        exact le_mul_of_one_le_right (poissonMass_nonneg hr j)
          ((Real.one_le_exp_iff).mpr (mul_nonneg hs (sub_nonneg.mpr hj')))
      _ = _ := by
        calc
          _ = Clock.poissonMass r j * (Real.exp (s*k)*Real.exp (-s*j)) := by
            rw [← Real.exp_add]; congr 2; ring
          _ = _ := by ring
  apply hle.trans
  have ht := Summable.sum_le_tsum (Finset.range k) (fun j _ => by
    exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (poissonMass_nonneg hr j) (Real.exp_pos _).le)) hsum.summable
  rw [hsum.tsum_eq] at ht
  simpa only [Real.exp_add] using ht

lemma exists_poisson_head_exponent {a : ℝ} (ha1 : a < 1) :
    ∃ s c : ℝ, 0 < s ∧ 0 < c ∧ s*a+Real.exp (-s)-1 = -c := by
  let s := (1-a)/2
  have hs : 0 < s := by dsimp [s]; linarith
  have he : Real.exp (-s) ≤ (1+s)⁻¹ := by
    rw [Real.exp_neg]
    simp only [← one_div]
    apply one_div_le_one_div_of_le (by linarith : 0 < 1+s)
    linarith [Real.add_one_le_exp s]
  have ha' : a*(1+s) < 1 := by
    have hm := mul_le_mul_of_nonneg_right ha1.le hs.le
    dsimp [s] at *
    nlinarith
  have hh : s*a+(1+s)⁻¹-1 < 0 := by
    have hpos : 0 < 1+s := by linarith
    have hid : (s*a+(1+s)⁻¹-1)*(1+s) = s*(a*(1+s)-1) := by
      field_simp
      ring
    have hp := mul_neg_of_pos_of_neg hs (sub_neg.mpr ha')
    rw [← hid] at hp
    nlinarith
  refine ⟨s, -(s*a+Real.exp (-s)-1),hs,?_,by ring⟩
  linarith

lemma continuousKernel_poisson_integral {n : ℕ} (hn : 0 < n)
    (g : Disorder n) (t : ℝ) (ht : 0 ≤ t) (x y : Spin n) :
    continuousKernel (coupling g) t x y = ∫ j, (transition g ^ j) x y
      ∂poissonMeasure (⟨(n:ℝ)*t, mul_nonneg (Nat.cast_nonneg n) ht⟩ : ℝ≥0) := by
  erw [integral_poissonMeasure]
  change continuousKernel (coupling g) t x y =
    ∑' j, Real.exp (-((n:ℝ)*t))*((n:ℝ)*t)^j/(j.factorial:ℝ)*(transition g ^ j) x y
  simpa only [neg_mul] using
    (continuousKernel_poisson_hasSum hn g t x y).tsum_eq.symm

lemma integrable_discreteKernel_poisson {n : ℕ} (g : Disorder n)
    (r : ℝ≥0) (x y : Spin n) :
    Integrable (fun j => (transition g ^ j) x y) (poissonMeasure r) := by
  apply Integrable.mono' (integrable_const (1 : ℝ)) (.of_discrete) (ae_of_all _ ?_)
  intro j
  rw [Real.norm_eq_abs, abs_of_nonneg ((transition_pow_stochastic g j).1 x y)]
  exact (Finset.single_le_sum (fun z _ => (transition_pow_stochastic g j).1 x z)
    (Finset.mem_univ y)).trans_eq
    (Matrix.sum_row_of_mem_rowStochastic (transition_pow_stochastic g j) x)

lemma totalVariation_integral_le {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Ω → Spin n → ℝ)
    (q : Spin n → ℝ) (hi : ∀ y, Integrable (fun j => p j y) μ) :
    totalVariation (fun y => ∫ j, p j y ∂μ) q ≤ ∫ j, totalVariation (p j) q ∂μ := by
  unfold totalVariation
  rw [integral_const_mul, integral_finsetSum]
  swap
  · intro y _
    exact ((hi y).sub (integrable_const (q y))).abs
  gcongr with y
  have he : (∫ j, p j y ∂μ)-q y = ∫ j, (p j y-q y) ∂μ := by
    rw [integral_sub (hi y) (integrable_const _)]
    simp
  rw [he]
  exact abs_integral_le_integral_abs

lemma integrable_totalVariation_poisson {n : ℕ} (g : Disorder n)
    (r : ℝ≥0) (x : Spin n) :
    Integrable (fun j => totalVariation ((transition g ^ j) x) (mass g 0))
      (poissonMeasure r) := by
  unfold totalVariation
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro y _
  exact ((integrable_discreteKernel_poisson g r x y).sub (integrable_const _)).abs

lemma poisson_head_integral (r : ℝ≥0) (k : ℕ) :
    (∫ j : ℕ, (if j < k then (1:ℝ) else 0) ∂poissonMeasure r) =
      ∑ j ∈ Finset.range k, Clock.poissonMass r j := by
  erw [integral_poissonMeasure]
  simp only [smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [tsum_eq_sum (s := Finset.range k) (fun j hj => by
    simp only [Finset.mem_range, not_lt] at hj
    simp only [not_lt.mpr hj, ite_false, if_false])]
  apply Finset.sum_congr rfl
  intro j hj
  rw [ite_eq_left (Finset.mem_range.mp hj)]
  rfl

lemma continuous_le_poisson_head_add_discrete {n : ℕ} (hn : 0 < n)
    (g : Disorder n) (t : ℝ) (ht : 0 ≤ t) (k : ℕ) :
    continuousDistance g t ≤ (∑ j ∈ Finset.range k, Clock.poissonMass ((n:ℝ)*t) j) +
      discreteDistance g k := by
  let r : ℝ≥0 := ⟨(n:ℝ)*t,mul_nonneg (Nat.cast_nonneg n) ht⟩
  apply Finset.sup'_le
  intro x _
  change totalVariation (continuousKernel (coupling g) t x) (mass g 0) ≤ _
  have he : continuousKernel (coupling g) t x =
      fun y => ∫ j, (transition g ^ j) x y ∂poissonMeasure r := by
    funext y
    exact continuousKernel_poisson_integral hn g t ht x y
  rw [he]
  apply (totalVariation_integral_le _ _ _ (integrable_discreteKernel_poisson g r x)).trans
  have hbi : Integrable (fun j : ℕ => if j < k then (1:ℝ) else 0) (poissonMeasure r) := by
    apply Integrable.mono' (integrable_const (1:ℝ)) (.of_discrete)
    exact ae_of_all _ (fun j => by split_ifs <;> norm_num)
  calc
    _ ≤ ∫ j : ℕ, (if j < k then (1:ℝ) else 0)+discreteDistance g k ∂poissonMeasure r := by
      apply integral_mono (integrable_totalVariation_poisson g r x)
        (hbi.add (integrable_const _))
      intro j
      change totalVariation ((transition g ^ j) x) (mass g 0) ≤
        (if j < k then (1:ℝ) else 0)+discreteDistance g k
      by_cases hj : j < k
      · simp only [ite_eq_left hj]
        have hb := (tv_le_discreteDistance g j x).trans (discreteDistance_le_one g j)
        linarith [discreteDistance_nonneg g k]
      · simp only [ite_eq_right hj, zero_add]
        exact (tv_le_discreteDistance g j x).trans
          (discreteDistance_antitone g (not_lt.mp hj))
    _ = _ := by
      rw [integral_add hbi (integrable_const _), poisson_head_integral]
      have hu : (poissonMeasure r).real Set.univ = 1 := by
        simp [Measure.real, measure_univ]
      simp only [integral_const, smul_eq_mul, hu, one_mul]
      rfl

lemma uniform_lower_clock_error
    (G : ∀ n : ℕ, Set (Disorder n)) {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (hdiv : ∀ R : ℝ, ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, R ≤ (n:ℝ)*medianTime g) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      (∑ j ∈ Finset.range ⌊(1-b)*(n:ℝ)*medianTime g⌋₊,
        Clock.poissonMass ((n:ℝ)*((1-b/2)*medianTime g)) j) < ε := by
  let a : ℝ := (1-b)/(1-b/2)
  have hmid : 0 < 1-b/2 := by linarith
  have ha1 : a < 1 := by
    apply (div_lt_one hmid).mpr
    linarith
  obtain ⟨s,c,hs,hc,he⟩ := exists_poisson_head_exponent ha1
  intro ε hε
  have hlim : Tendsto (fun z : ℝ => Real.exp (-c*((1-b/2)*z))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,neg_mul,id_eq] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        ((tendsto_id.const_mul_atTop hmid).const_mul_atTop hc)
  obtain ⟨R,hR⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
  filter_upwards [hdiv R] with n hn
  intro g hg
  have ht := (medianTime_mem g).1
  have hr : 0 ≤ (n:ℝ)*((1-b/2)*medianTime g) := by positivity
  have hkr : (⌊(1-b)*(n:ℝ)*medianTime g⌋₊:ℝ) ≤
      a*((n:ℝ)*((1-b/2)*medianTime g)) := by
    apply (Nat.floor_le (mul_nonneg
      (mul_nonneg (by linarith) (Nat.cast_nonneg _)) ht)).trans
    apply le_of_eq
    dsimp [a]
    have hne : 2-b ≠ 0 := by linarith
    field_simp [hne]
  have hhead := poisson_head_le hr hs.le ⌊(1-b)*(n:ℝ)*medianTime g⌋₊
  have hexp : Real.exp (s*(⌊(1-b)*(n:ℝ)*medianTime g⌋₊:ℝ)+
      ((n:ℝ)*((1-b/2)*medianTime g))*(Real.exp (-s)-1)) ≤
        Real.exp (-c*((1-b/2)*((n:ℝ)*medianTime g))) := by
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ s*(a*((n:ℝ)*((1-b/2)*medianTime g)))+
          ((n:ℝ)*((1-b/2)*medianTime g))*(Real.exp (-s)-1) := by
        gcongr
      _ = (s*a+Real.exp (-s)-1)*((n:ℝ)*((1-b/2)*medianTime g)) := by ring
      _ = _ := by rw [he]; ring
  exact (hhead.trans hexp).trans_lt (hR _ (hn g hg))

theorem uniform_discrete_lower_from_continuous
    (G : ∀ n : ℕ, Set (Disorder n)) {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (hdiv : ∀ R : ℝ, ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, R ≤ (n:ℝ)*medianTime g)
    (hcont : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      1-δ < continuousDistance g ((1-b/2)*medianTime g)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      1-δ < discreteDistance g ⌊(1-b)*(n:ℝ)*medianTime g⌋₊ := by
  intro δ hδ
  filter_upwards [hcont (δ/2) (by positivity),
    uniform_lower_clock_error G hb hb1 hdiv (δ/2) (by positivity),
    eventually_gt_atTop 0] with n hn he hn0
  intro g hg
  have h := continuous_le_poisson_head_add_discrete hn0 g ((1-b/2)*medianTime g)
    (mul_nonneg (by linarith) (medianTime_mem g).1) ⌊(1-b)*(n:ℝ)*medianTime g⌋₊
  have hc := hn g hg
  have he' := he g hg
  linarith

end SKRatio.Calculus

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Dynamics_StepMass
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SKRatioClock.Clock

theorem scheffe_density_filter {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ι → α → ℝ} {g : α → ℝ}
    (hf : ∀ᶠ n in l, Integrable (f n) μ) (hg : Integrable g μ)
    (hf0 : ∀ᶠ n in l, ∀ᵐ x ∂μ, 0 ≤ f n x) (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) l (𝓝 (g x)))
    (hmass : Tendsto (fun n => ∫ x, f n x ∂μ) l (𝓝 (∫ x, g x ∂μ))) :
    Tendsto (fun n => ∫ x, |f n x-g x| ∂μ) l (𝓝 0) := by
  have hmin : Tendsto (fun n => ∫ x, min (f n x) (g x) ∂μ)
      l (𝓝 (∫ x, g x ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence g
    · filter_upwards [hf] with n hn
      exact hn.aestronglyMeasurable.inf hg.aestronglyMeasurable
    · filter_upwards [hf0] with n hn
      filter_upwards [hn,hg0] with x hx hy
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min hx hy)]
      exact min_le_right _ _
    · exact hg
    · filter_upwards [hlim] with x hx
      simpa using hx.min (tendsto_const_nhds (x := g x))
  have ht := (hmass.add (tendsto_const_nhds (x := ∫ x, g x ∂μ))).sub
    (hmin.const_mul 2)
  have hz : (∫ x, g x ∂μ)+(∫ x, g x ∂μ)-2*(∫ x, g x ∂μ)=0 := by ring
  rw [hz] at ht
  apply ht.congr'
  filter_upwards [hf] with n hn
  rw [← integral_add hn hg, ← integral_const_mul]
  have hi : Integrable (fun x => f n x+g x) μ := hn.add hg
  have hj : Integrable (fun x => 2*min (f n x) (g x)) μ := (hn.inf hg).const_mul 2
  rw [← integral_sub hi hj]
  congr 1
  ext x
  rcases le_total (f n x) (g x) with h|h
  · rw [min_eq_left h,abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h,abs_of_nonneg (sub_nonneg.mpr h)]
    ring

lemma stepMass_of_nonneg (p : ℕ → ℝ) {x : ℝ} (hx : 0 ≤ x) :
    stepMass p x = p ⌊x⌋₊ := by
  unfold stepMass
  rw [tsum_eq_single ⌊x⌋₊]
  · exact Set.indicator_of_mem (show x ∈ Set.Ico (⌊x⌋₊:ℝ) (⌊x⌋₊+1) from
      ⟨Nat.floor_le hx,Nat.lt_floor_add_one x⟩) _
  · intro j hj
    apply Set.indicator_of_notMem
    intro h
    exact hj ((Nat.floor_eq_iff hx).mpr h).symm

lemma stepMass_of_neg (p : ℕ → ℝ) {x : ℝ} (hx : x < 0) : stepMass p x = 0 := by
  unfold stepMass
  suffices hh : (fun j : ℕ => (Set.Ico (j:ℝ) (j+1)).indicator (fun _ => p j) x) = 0 by
    rw [hh]
    change (∑' _ : ℕ, (0:ℝ)) = 0
    exact tsum_zero
  ext j
  apply Set.indicator_of_notMem
  intro h
  exact (not_le.mpr hx) ((Nat.cast_nonneg j).trans h.1)

lemma stepMass_nonneg {p : ℕ → ℝ} (hp : ∀ j, 0 ≤ p j) (x : ℝ) : 0 ≤ stepMass p x := by
  by_cases hx : 0 ≤ x
  · rw [stepMass_of_nonneg p hx]
    exact hp _
  · rw [stepMass_of_neg p (lt_of_not_ge hx)]

lemma integral_step_interval (p : ℕ → ℝ) (j : ℕ) :
    ∫ x : ℝ, (Set.Ico (j:ℝ) (j+1)).indicator (fun _ => p j) x = p j := by
  rw [integral_indicator measurableSet_Ico,integral_const]
  simp [Measure.real,Real.volume_Ico]

lemma integrable_step_interval (p : ℕ → ℝ) (j : ℕ) :
    Integrable ((Set.Ico (j:ℝ) (j+1)).indicator (fun _ => p j)) :=
  (integrableOn_const (μ := volume) (C := p j) (by simp [Real.volume_Ico])).integrable_indicator
    measurableSet_Ico

lemma integral_step_interval_norm (p : ℕ → ℝ) (j : ℕ) :
    ∫ x : ℝ, ‖(Set.Ico (j:ℝ) (j+1)).indicator (fun _ => p j) x‖ = |p j| := by
  rw [← integral_step_interval (fun j => |p j|) j]
  congr 1
  ext x
  by_cases hx : x ∈ Set.Ico (j:ℝ) (j+1)
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

lemma integral_stepMass {p : ℕ → ℝ} (hp : Summable p) :
    ∫ x, stepMass p x = ∑' j, p j := by
  unfold stepMass
  rw [← integral_tsum_of_summable_integral_norm (integrable_step_interval p)]
  · simp only [integral_step_interval]
  · simpa only [integral_step_interval_norm] using hp.abs

lemma integrable_stepMass {p : ℕ → ℝ} (hp : HasSum p 1) : Integrable (stepMass p) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_stepMass hp.summable,hp.tsum_eq]
  norm_num

lemma integrable_histogram {p : ℕ → ℝ} (hp : HasSum p 1) (q : ℝ) {n : ℕ}
    (hn : 0 < n) : Integrable (histogram q n p) := by
  have hs : Real.sqrt (n:ℝ) ≠ 0 := by positivity
  have hi := ((integrable_stepMass hp).comp_add_right (q*n)).comp_mul_right' hs
  convert! hi.const_mul (Real.sqrt (n:ℝ)) using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [histogram,add_comm]

lemma integral_histogram {p : ℕ → ℝ} (hp : HasSum p 1) (q : ℝ) {n : ℕ}
    (hn : 0 < n) : ∫ x, histogram q n p x = 1 := by
  have hs : Real.sqrt (n:ℝ) ≠ 0 := by positivity
  unfold histogram
  rw [integral_const_mul]
  have hh : (fun x : ℝ => stepMass p (q*n+x*Real.sqrt n)) =
      (fun x : ℝ => (fun t => stepMass p (t+q*n)) (Real.sqrt n*x)) := by
    ext x
    congr 1
    ring
  rw [hh,Measure.integral_comp_mul_left (fun t : ℝ => stepMass p (t+q*n))
    (Real.sqrt (n:ℝ)),integral_add_right_eq_self,
    integral_stepMass hp.summable,hp.tsum_eq,smul_eq_mul,mul_one,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),mul_inv_cancel₀ hs]

lemma histogram_nonneg {p : ℕ → ℝ} (hp : ∀ j, 0 ≤ p j) (q : ℝ) (n : ℕ) (x : ℝ) :
    0 ≤ histogram q n p x :=
  mul_nonneg (Real.sqrt_nonneg _) (stepMass_nonneg hp _)

end SKRatioClock.Clock

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Dynamics_SumPoissonMass
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SKRatioClock.Clock

lemma hasSum_poissonMass (m : ℝ) : HasSum (poissonMass m) 1 := by
  convert! (NormedSpace.expSeries_div_hasSum_exp m).mul_left (Real.exp (-m)) using 1
  · ext n
    simp only [poissonMass,mul_div_assoc]
  · simp [← Real.exp_eq_exp_ℝ, ← Real.exp_add]

lemma hasSum_binomialMass (q : ℝ) (n : ℕ) : HasSum (binomialMass q n) 1 := by
  have hh : HasSum (binomialMass q n)
      (∑ k ∈ Finset.range (n+1), binomialMass q n k) :=
    hasSum_sum_of_ne_finset_zero (s := Finset.range (n+1))
    (f := binomialMass q n) (by
      intro k hk
      have hnk : n < k := by simpa only [Finset.mem_range,not_lt,Nat.add_one_le_iff] using hk
      simp only [binomialMass,Nat.choose_eq_zero_of_lt hnk,Nat.cast_zero,zero_mul])
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  have hb := add_pow q (1-q) n
  have hq : q+(1-q)=1 := by ring
  rw [hq,one_pow] at hb
  rw [hb]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [binomialMass]
  ring

lemma poisson_density_pointwise {q : ℝ} (hq : 0 < q) (y x : ℝ) :
    Tendsto (fun n : ℕ => histogram q n (poissonMass (q*n+y*Real.sqrt n)) x)
      atTop (𝓝 (gaussianPDFReal y ⟨q,hq.le⟩ x)) := by
  have hh := poisson_histogram_pointwise hq x y
  rw [gaussian_formula hq x y] at hh
  apply hh.congr'
  filter_upwards [(center_tendsto_atTop hq x).eventually (eventually_ge_atTop 0)] with n hn
  simp only [histogram,stepMass_of_nonneg _ hn,centralIndex]

lemma binomial_density_pointwise {q : ℝ} (hql : 0 < q) (hqu : q < 1) (x : ℝ) :
    Tendsto (fun n : ℕ => histogram q n (binomialMass q n) x)
      atTop (𝓝 (gaussianPDFReal 0 ⟨q*(1-q),mul_nonneg hql.le (by linarith)⟩ x)) := by
  apply (binomial_histogram_pointwise hql hqu x).congr'
  filter_upwards [(center_tendsto_atTop hql x).eventually (eventually_ge_atTop 0)] with n hn
  simp only [histogram,stepMass_of_nonneg _ hn,centralIndex]

theorem poisson_density_L1 {q : ℝ} (hq : 0 < q) (y : ℝ) :
    Tendsto (fun n : ℕ => ∫ x : ℝ,
      |histogram q n (poissonMass (q*n+y*Real.sqrt n)) x-
        gaussianPDFReal y ⟨q,hq.le⟩ x|) atTop (𝓝 0) := by
  apply scheffe_density_filter
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact integrable_histogram (hasSum_poissonMass _) q hn
  · exact integrable_gaussianPDFReal _ _
  · filter_upwards [(center_tendsto_atTop hq y).eventually (eventually_ge_atTop 0)] with n hn
    exact Filter.Eventually.of_forall (histogram_nonneg (fun j => by
      unfold poissonMass
      positivity) q n)
  · exact Filter.Eventually.of_forall (gaussianPDFReal_nonneg _ _)
  · exact Filter.Eventually.of_forall (poisson_density_pointwise hq y)
  · have hv : (⟨q,hq.le⟩ : ℝ≥0) ≠ 0 := by
      intro h
      have hh := congrArg (fun r : ℝ≥0 => (r:ℝ)) h
      exact hq.ne' hh
    rw [integral_gaussianPDFReal_eq_one _ hv]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact (integral_histogram (hasSum_poissonMass _) q hn).symm

theorem binomial_density_L1 {q : ℝ} (hql : 0 < q) (hqu : q < 1) :
    Tendsto (fun n : ℕ => ∫ x : ℝ,
      |histogram q n (binomialMass q n) x-
        gaussianPDFReal 0 ⟨q*(1-q),mul_nonneg hql.le (by linarith)⟩ x|) atTop (𝓝 0) := by
  apply scheffe_density_filter
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact integrable_histogram (hasSum_binomialMass q n) q hn
  · exact integrable_gaussianPDFReal _ _
  · apply Filter.Eventually.of_forall
    intro n
    exact Filter.Eventually.of_forall (histogram_nonneg (fun j => by
      unfold binomialMass
      positivity) q n)
  · exact Filter.Eventually.of_forall (gaussianPDFReal_nonneg _ _)
  · exact Filter.Eventually.of_forall (binomial_density_pointwise hql hqu)
  · have hv : (⟨q*(1-q),mul_nonneg hql.le (by linarith)⟩ : ℝ≥0) ≠ 0 := by
      intro h
      have hh := congrArg (fun r : ℝ≥0 => (r:ℝ)) h
      exact (mul_pos hql (by linarith : 0 < 1-q)).ne' hh
    rw [integral_gaussianPDFReal_eq_one _ hv]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact (integral_histogram (hasSum_binomialMass q n) q hn).symm

end SKRatioClock.Clock

open MeasureTheory Filter
open scoped Topology NNReal ENNReal

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Dynamics_ClockBridge
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
attribute [-simp] _root_.OAI.SKRatio.Calculus.continuousDistance_zero _root_.OAI.SKRatio.Calculus.continuousKernel_zero _root_.OAI.SKRatio.Calculus.field_reversal _root_.OAI.SKRatio.Calculus.gibbsEuclideanEquiv_apply _root_.OAI.SKRatio.Calculus.lift_scalarEigenfunction _root_.OAI.SKRatio.Calculus.mass_reversal _root_.OAI.SKRatio.Calculus.reversal_reversal _root_.OAI.SKRatio.Calculus.spin_reversal _root_.OAI.SKRatio.Calculus.stationaryPairingCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap MeasureTheory Filter ProbabilityTheory SKRatioClock
namespace SKRatio.Calculus

lemma kernel_apply {n : ℕ} (K : Observables n →L[ℝ] Observables n)
    (f : Observables n) (x : Spin n) :
    (∑ y, K (fun z => if z = y then 1 else 0) x*f y) = K f x := by
  conv_rhs => rw [observable_basis f]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

lemma attemptKernel_nonneg {n : ℕ} (J : Interaction n) (x y : Spin n) :
    0 ≤ attemptKernel J x y := by
  classical
  exact attempt_nonneg J _ (fun z => by split_ifs <;> norm_num) x

lemma attemptKernel_eq_transition {n : ℕ} (g : Disorder n) :
    attemptKernel (coupling g) = transition g := by
  classical
  funext x y
  simp [attemptKernel, attempt_eq_transition, Matrix.mulVec, dotProduct]

lemma residualAttempt_apply {n : ℕ} (J : Interaction n) (q : ℝ)
    (f : Observables n) (x : Spin n) :
    residualAttempt J q f x = (attemptLM J f x-(1-q)*f x)/q := by
  simp [residualAttempt,div_eq_mul_inv,mul_comm]

lemma attempt_eq_lazy_residual {n : ℕ} (J : Interaction n) {q : ℝ} (hq : q ≠ 0) :
    attemptLM J = q • residualAttempt J q+(1-q) • 1 := by
  simp only [residualAttempt,smul_smul,mul_inv_cancel₀ hq,one_smul,sub_add_cancel]

lemma residualAttempt_const {n : ℕ} (J : Interaction n) {q : ℝ} (hq : q ≠ 0)
    (c : ℝ) : residualAttempt J q (fun _ => c) = fun _ => c := by
  ext x
  rw [residualAttempt_apply,attempt_const]
  field_simp
  ring

lemma residualAttempt_pow_const {n : ℕ} (J : Interaction n) {q : ℝ} (hq : q ≠ 0)
    (k : ℕ) (c : ℝ) : (residualAttempt J q ^ k) (fun _ => c) = fun _ => c := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ',mul_apply_eq_comp,ih,residualAttempt_const J hq]

lemma residualAttempt_nonneg {n : ℕ} (J : Interaction n) {q : ℝ} (hq : 0 < q)
    (hhold : ∀ x, 1-q ≤ attemptKernel J x x)
    (f : Observables n) (hf : ∀ x, 0 ≤ f x) (x : Spin n) :
    0 ≤ residualAttempt J q f x := by
  rw [← kernel_apply (residualAttempt J q) f x]
  apply Finset.sum_nonneg
  intro y _
  apply mul_nonneg _ (hf y)
  rw [residualAttempt_apply]
  apply div_nonneg _ hq.le
  by_cases hxy : x=y
  · subst y
    simpa [attemptKernel] using sub_nonneg.mpr (hhold x)
  · simpa only [hxy,↓reduceIte,mul_zero,sub_zero,attemptKernel] using
      attemptKernel_nonneg J x y

lemma residualAttempt_pow_nonneg {n : ℕ} (J : Interaction n) {q : ℝ} (hq : 0 < q)
    (hhold : ∀ x, 1-q ≤ attemptKernel J x x)
    (k : ℕ) (f : Observables n) (hf : ∀ x, 0 ≤ f x) (x : Spin n) :
    0 ≤ (residualAttempt J q ^ k) f x := by
  induction k generalizing x with
  | zero => exact hf x
  | succ k ih =>
    rw [pow_succ',mul_apply_eq_comp]
    exact residualAttempt_nonneg J hq hhold _ (fun x => ih x) x

lemma residualAttempt_pow_abs_le {n : ℕ} (J : Interaction n) {q : ℝ} (hq : 0 < q)
    (hhold : ∀ x, 1-q ≤ attemptKernel J x x)
    (k : ℕ) (f : Observables n) (hf : ∀ x, |f x| ≤ 1) (x : Spin n) :
    |(residualAttempt J q ^ k) f x| ≤ 1 := by
  have hup := residualAttempt_pow_nonneg J hq hhold k (fun y => 1-f y)
    (fun y => by have := (abs_le.mp (hf y)).2; linarith) x
  have hlo := residualAttempt_pow_nonneg J hq hhold k (fun y => f y+1)
    (fun y => by have := (abs_le.mp (hf y)).1; linarith) x
  change 0 ≤ (residualAttempt J q ^ k) ((fun _ => 1)-f) x at hup
  change 0 ≤ (residualAttempt J q ^ k) (f+(fun _ => 1)) x at hlo
  rw [map_sub,residualAttempt_pow_const J hq.ne'] at hup
  rw [map_add,residualAttempt_pow_const J hq.ne'] at hlo
  simp only [Pi.add_apply,Pi.sub_apply] at hlo hup
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma residual_semigroup_uniformization {n : ℕ} (hn : 0 < n)
    (J : Interaction n) {q : ℝ} (hq : q ≠ 0) (t : ℝ) :
    semigroup J t = Real.exp (-(q*n*t)) •
      NormedSpace.exp ((q*n*t) • residualAttempt J q) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have heq : t • generatorCLM J =
      (-(q*n*t)) • (1 : Observables n →L[ℝ] Observables n) +
        (q*n*t) • residualAttempt J q := by
    unfold residualAttempt attemptLM
    simp only [smul_smul,smul_sub,smul_add]
    have hc : q*n*t*q⁻¹ = (n:ℝ)*t := by field_simp
    have hc' : q*n*t*(q⁻¹*(n:ℝ)⁻¹) = t := by field_simp
    have hc'' : q*n*t*(q⁻¹*(1-q)) = (n:ℝ)*t*(1-q) := by field_simp
    rw [hc,hc',hc'']
    module
  let : NormedAlgebra ℚ (Observables n →L[ℝ] Observables n) :=
    NormedAlgebra.restrictScalars ℚ ℝ _
  unfold semigroup
  rw [heq,NormedSpace.exp_add_of_commute
    (((Commute.one_left (residualAttempt J q)).smul_left _).smul_right _),
    exp_smul_identity,smul_mul_assoc,one_mul]

lemma residual_poisson_hasSum {n : ℕ} (hn : 0 < n)
    (J : Interaction n) {q : ℝ} (hq : q ≠ 0) (t : ℝ)
    (f : Observables n) (x : Spin n) :
    HasSum (fun j => Clock.poissonMass (q*n*t) j*(residualAttempt J q ^ j) f x)
      (semigroup J t f x) := by
  have hs := (Pi.hasSum.mp (exp_apply_hasSum ((q*n*t) • residualAttempt J q) f) x).mul_left
    (Real.exp (-(q*n*t)))
  convert! hs using 1
  · funext j
    simp only [smul_pow,_root_.smul_apply,Pi.smul_apply,smul_eq_mul,Clock.poissonMass]
    ring
  · rw [residual_semigroup_uniformization hn J hq]
    rfl

lemma natCastCLM_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (f : E) : (k : E →L[ℝ] E) f = (k:ℝ) • f := by
  induction k with
  | zero => simp
  | succ k ih => simp [Nat.cast_succ,ih,add_smul]

lemma residual_binomial_sum {n : ℕ} (J : Interaction n) {q : ℝ} (hq : q ≠ 0)
    (M : ℕ) (f : Observables n) (x : Spin n) :
    (∑ j ∈ Finset.range (M+1), Clock.binomialMass q M j*
      (residualAttempt J q ^ j) f x) = (attemptLM J ^ M) f x := by
  rw [attempt_eq_lazy_residual J hq]
  rw [(((Commute.one_right (residualAttempt J q)).smul_left q).smul_right (1-q)).add_pow]
  simp only [_root_.sum_apply,smul_pow,one_pow,smul_mul_assoc,mul_smul_comm,mul_one,
    Clock.binomialMass,mul_apply_eq_comp,_root_.smul_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  simp only [natCastCLM_apply,map_smul,Pi.smul_apply,smul_eq_mul]
  ring

lemma residual_binomial_hasSum {n : ℕ} (J : Interaction n) {q : ℝ} (hq : q ≠ 0)
    (M : ℕ) (f : Observables n) (x : Spin n) :
    HasSum (fun j => Clock.binomialMass q M j*(residualAttempt J q ^ j) f x)
      ((attemptLM J ^ M) f x) := by
  rw [← residual_binomial_sum J hq M f x]
  apply hasSum_sum_of_ne_finset_zero
  intro j hj
  have hj' : M < j := by simp only [Finset.mem_range,not_lt] at hj; omega
  simp [Clock.binomialMass,Nat.choose_eq_zero_of_lt hj']

lemma gibbsMean_abs_le_one {n : ℕ} (g : Disorder n) (f : Observables n)
    (hf : ∀ x, |f x| ≤ 1) : |FiniteLaw.mean (mass g 0) f| ≤ 1 := by
  unfold FiniteLaw.mean
  calc
    _ ≤ ∑ x, |mass g 0 x*f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, mass g 0 x := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul,abs_of_nonneg (mass_nonneg g 0 x)]
      exact mul_le_of_le_one_right (mass_nonneg g 0 x) (hf x)
    _ = _ := sum_mass g 0

lemma residual_test_bound {n : ℕ} (g : Disorder n) {q : ℝ} (hq : 0 < q)
    (hhold : ∀ x, 1-q ≤ transition g x x)
    (f : Observables n) (hf : ∀ x, |f x| ≤ 1) (x : Spin n) (j : ℕ) :
    |(residualAttempt (coupling g) q ^ j) f x-FiniteLaw.mean (mass g 0) f| ≤ 2 := by
  have h := abs_sub ((residualAttempt (coupling g) q ^ j) f x)
    (FiniteLaw.mean (mass g 0) f)
  have hhold' : ∀ x, 1-q ≤ attemptKernel (coupling g) x x := by
    rwa [attemptKernel_eq_transition]
  linarith [residualAttempt_pow_abs_le (coupling g) hq hhold' j f hf x,
    gibbsMean_abs_le_one g f hf]

lemma residual_poisson_test {n : ℕ} (hn : 0 < n)
    (g : Disorder n) {q : ℝ} (hq : q ≠ 0) (m : ℝ)
    (f : Observables n) (x : Spin n) :
    (∑' j, Clock.poissonMass m j*((residualAttempt (coupling g) q ^ j) f x-
      FiniteLaw.mean (mass g 0) f)) =
      semigroup (coupling g) (m/(q*n)) f x-FiniteLaw.mean (mass g 0) f := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have he : q*n*(m/(q*n)) = m := by field_simp
  have hs := residual_poisson_hasSum hn (coupling g) hq (m/(q*n)) f x
  rw [he] at hs
  have hh := hs.sub ((Clock.hasSum_poissonMass m).mul_right (FiniteLaw.mean (mass g 0) f))
  simpa only [one_mul,← mul_sub] using hh.tsum_eq

lemma residual_binomial_test {n : ℕ} (g : Disorder n) {q : ℝ} (hq : q ≠ 0)
    (M : ℕ) (f : Observables n) (x : Spin n) :
    (∑' j, Clock.binomialMass q M j*((residualAttempt (coupling g) q ^ j) f x-
      FiniteLaw.mean (mass g 0) f)) =
      ((transition g ^ M) *ᵥ f) x-FiniteLaw.mean (mass g 0) f := by
  have hs := residual_binomial_hasSum (coupling g) hq M f x
  have hh := hs.sub ((Clock.hasSum_binomialMass q M).mul_right (FiniteLaw.mean (mass g 0) f))
  simpa only [one_mul,← mul_sub, attempt_pow_eq_transition_pow] using hh.tsum_eq

lemma totalVariation_test_bound {n : ℕ} (p r f : Spin n → ℝ)
    (hf : ∀ y, |f y| ≤ 1) :
    |FiniteLaw.mean p f-FiniteLaw.mean r f| ≤ 2*totalVariation p r := by
  unfold FiniteLaw.mean
  rw [← Finset.sum_sub_distrib]
  simp_rw [← sub_mul]
  calc
    _ ≤ ∑ y, |(p y-r y)*f y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y, |p y-r y| := by
      apply Finset.sum_le_sum
      intro y _
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hf y)
    _ = _ := by dsimp [totalVariation]; ring

lemma continuous_test_bound {n : ℕ} (g : Disorder n) (t : ℝ)
    (f : Observables n) (hf : ∀ y, |f y| ≤ 1) (x : Spin n) :
    |semigroup (coupling g) t f x-FiniteLaw.mean (mass g 0) f| ≤
      2*continuousDistance g t := by
  rw [semigroup_eq_kernel]
  apply (totalVariation_test_bound (continuousKernel (coupling g) t x) (mass g 0) f hf).trans
  exact mul_le_mul_of_nonneg_left (tv_le_continuousDistance g t x) (by norm_num)

lemma field_square_sum_le {n : ℕ} (J : Interaction n) (x : Spin n)
    {K : ℝ} (_hK : 0 ≤ K)
    (hJ : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) J‖ ≤ K) :
    ∑ i, field J x i^2 ≤ K^2*(n:ℝ) := by
  let A := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) J
  let v : EuclideanSpace ℝ (Fin n) := (WithLp.equiv 2 _).symm (spin x)
  have hv : ‖v‖^2 = (n:ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [v, spin_sq]
  have hh : ‖A v‖ ≤ K*‖v‖ := (A.le_opNorm v).trans
    (mul_le_mul_of_nonneg_right hJ (norm_nonneg _))
  have hs := pow_le_pow_left₀ (norm_nonneg _) hh 2
  rw [mul_pow, hv, EuclideanSpace.real_norm_sq_eq] at hs
  exact hs

lemma one_sub_tanh_half (a : ℝ) :
    (1-Real.tanh a)/2 = 1/(1+Real.exp (2*a)) := by
  have hh := exp_two_mul_one_sub_tanh a
  have he := Real.exp_pos (2*a)
  apply (eq_div_iff (by positivity : (1+Real.exp (2*a)) ≠ 0)).mpr
  nlinarith

lemma one_add_tanh_half (a : ℝ) :
    (1+Real.tanh a)/2 = 1/(1+Real.exp (-2*a)) := by
  simpa only [Real.tanh_neg, sub_neg_eq_add, mul_neg, neg_mul] using one_sub_tanh_half (-a)

lemma siteRefresh_diagonal_lower {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) :
    1/(1+Real.exp (2*|field J x i|)) ≤
      siteRefresh J i (fun z => if z=x then 1 else 0) x := by
  have htrue : replace x i true = x ↔ x i = true := by
    constructor
    · intro h; simpa using (congrFun h i).symm
    · intro h; simpa only [h] using replace_self x i
  have hfalse : replace x i false = x ↔ x i = false := by
    constructor
    · intro h; simpa using (congrFun h i).symm
    · intro h; simpa only [h] using replace_self x i
  simp only [siteRefresh, htrue, hfalse, mean]
  cases x i <;> simp only [ Bool.false_eq_true, Bool.true_eq_false,
    ↓reduceIte, mul_zero, mul_one, zero_add, add_zero]
  · rw [one_sub_tanh_half]
    apply one_div_le_one_div_of_le (by positivity)
    apply add_le_add le_rfl
    apply Real.exp_le_exp.mpr
    linarith [le_abs_self (field J x i)]
  · rw [one_add_tanh_half]
    apply one_div_le_one_div_of_le (by positivity)
    apply add_le_add le_rfl
    apply Real.exp_le_exp.mpr
    linarith [neg_le_abs (field J x i)]

lemma logistic_quadratic_lower {a L : ℝ} (hL : 0 < L) :
    (1-a^2/L^2)/(1+Real.exp (2*L)) ≤ 1/(1+Real.exp (2*|a|)) := by
  by_cases ha : |a| ≤ L
  · calc
      _ ≤ 1/(1+Real.exp (2*L)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have : 0 ≤ a^2/L^2 := by positivity
        linarith
      _ ≤ _ := by
        apply one_div_le_one_div_of_le (by positivity)
        apply add_le_add le_rfl
        apply Real.exp_le_exp.mpr
        linarith
  · have ha2 : L^2 ≤ a^2 := by nlinarith [sq_abs a, abs_nonneg a, le_of_not_ge ha]
    have hratio : 1 ≤ a^2/L^2 := (one_le_div (sq_pos_of_pos hL)).mpr ha2
    exact (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)).trans (by positivity)

lemma attempted_holding_lower {n : ℕ} (hn : 0 < n) (J : Interaction n)
    {K : ℝ} (hK : 0 < K)
    (hJ : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) J‖ ≤ K) (x : Spin n) :
    1/(2*(1+Real.exp (2*(Real.sqrt 2*K)))) ≤ attemptKernel J x x := by
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hL : 0 < Real.sqrt 2*K := mul_pos (Real.sqrt_pos.mpr (by norm_num)) hK
  have hL2 : (Real.sqrt 2*K)^2 = 2*K^2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hsum := field_square_sum_le J x hK.le hJ
  have hs : (∑ i, (1-field J x i^2/(Real.sqrt 2*K)^2)/(1+Real.exp (2*(Real.sqrt 2*K)))) ≤
      ∑ i, siteRefresh J i (fun z => if z=x then 1 else 0) x := by
    apply Finset.sum_le_sum
    intro i _
    exact (logistic_quadratic_lower hL).trans (siteRefresh_diagonal_lower J x i)
  simp only [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, hL2] at hs
  have hf : (∑ i, field J x i^2)/(2*K^2) ≤ (n:ℝ)/2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2*K^2)).mpr
    nlinarith
  change _ ≤ attemptLM J (fun z => if z=x then 1 else 0) x
  rw [attempt_apply_of_pos hn]
  apply (le_div_iff₀ hnR).mpr
  calc
    _ = ((n:ℝ)/2)/(1+Real.exp (2*(Real.sqrt 2*K))) := by field_simp
    _ ≤ ((n:ℝ)-(∑ i, field J x i^2)/(2*K^2))/(1+Real.exp (2*(Real.sqrt 2*K))) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
    _ ≤ _ := hs

end SKRatio.Calculus

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Dynamics_GaussMoment
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology _root_.OAI.SKRatioGaussian.instNonemptyUnitBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace SKRatioClock.Clock

lemma hasDerivAt_gaussMoment (a : ℝ) (k : ℕ) (x : ℝ) :
    HasDerivAt (gaussMoment a k)
      ((k:ℝ)*gaussMoment a (k-1) x-2*a*gaussMoment a (k+1) x) x := by
  have he := ((((hasDerivAt_id x).pow 2).const_mul (-a)).exp)
  convert! ((hasDerivAt_id x).pow k).mul he using 1
  all_goals try with_reducible_and_instances rfl
  simp only [gaussMoment,pow_succ,Pi.pow_apply,id_eq,Nat.cast_ofNat,mul_one,pow_zero]
  ring

lemma integrable_abs_add_one_pow_gauss {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Integrable (fun x : ℝ => (|x|+1)^k*Real.exp (-a*x^2)) := by
  have hi (j : ℕ) : Integrable (fun x : ℝ => |x|^j*Real.exp (-a*x^2)) := by
    simpa only [gaussMoment,Real.norm_eq_abs,abs_mul,abs_pow,
      abs_of_nonneg (Real.exp_nonneg _)] using (integrable_gaussMoment ha j).norm
  have hh := integrable_finsetSum (Finset.range (k+1))
    (fun j _ => (hi j).mul_const (k.choose j:ℝ))
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  rw [add_pow,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [one_pow,mul_one]
  ring

lemma integrable_momentEnvelope {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Integrable (momentEnvelope a k) := by
  have hhalf : 0 < a/2 := by positivity
  have hh := (((integrable_abs_add_one_pow_gauss hhalf (k-1)).const_mul (k:ℝ)).add
    ((integrable_abs_add_one_pow_gauss hhalf (k+1)).const_mul (2*a))).const_mul (Real.exp a)
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [momentEnvelope,Pi.add_apply]
  ring

lemma gaussMoment_deriv_bound {a : ℝ} (ha : 0 < a) (k : ℕ) (x z : ℝ)
    (hz : z ∈ Set.Icc (x-1) (x+1)) :
    |(k:ℝ)*gaussMoment a (k-1) z-2*a*gaussMoment a (k+1) z| ≤
      momentEnvelope a k x := by
  have hdist : |z-x| ≤ 1 := abs_le.mpr ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hzabs : |z| ≤ |x|+1 := by
    calc
      |z| = |(z-x)+x| := by rw [sub_add_cancel]
      _ ≤ |z-x|+|x| := abs_add_le _ _
      _ ≤ |x|+1 := by linarith
  have hsq : (z-x)^2 ≤ 1 := by
    have hh := mul_self_le_mul_self (abs_nonneg (z-x)) hdist
    nlinarith [sq_abs (z-x)]
  have hquad : x^2/2-1 ≤ z^2 := by nlinarith [sq_nonneg (x-2*z)]
  have he : Real.exp (-a*z^2) ≤ Real.exp a*Real.exp (-(a/2)*x^2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hquad)]
  have h1 := pow_le_pow_left₀ (abs_nonneg z) hzabs (k-1)
  have h2 := pow_le_pow_left₀ (abs_nonneg z) hzabs (k+1)
  calc
    _ ≤ |(k:ℝ)*gaussMoment a (k-1) z|+|2*a*gaussMoment a (k+1) z| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le
        ((k:ℝ)*gaussMoment a (k-1) z) (2*a*gaussMoment a (k+1) z)
    _ = ((k:ℝ)*|z|^(k-1)+2*a*|z|^(k+1))*Real.exp (-a*z^2) := by
      norm_num only [gaussMoment,abs_mul,abs_pow,abs_of_nonneg (Nat.cast_nonneg k : (0:ℝ)≤k),
        abs_of_nonneg ha.le,abs_of_nonneg (Real.exp_nonneg _)]
      ring
    _ ≤ ((k:ℝ)*(|x|+1)^(k-1)+2*a*(|x|+1)^(k+1))*
        (Real.exp a*Real.exp (-(a/2)*x^2)) := by
      apply mul_le_mul _ he (Real.exp_nonneg _) (by positivity)
      exact add_le_add (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ = _ := by dsimp [momentEnvelope]; ring

lemma diffMoment_bound {a : ℝ} (ha : 0 < a) (k : ℕ) {h : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (x : ℝ) :
    |diffMoment a k h x| ≤ momentEnvelope a k x := by
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.Icc (x-1) (x+1))
    (f := gaussMoment a k)
    (f' := fun z => (k:ℝ)*gaussMoment a (k-1) z-2*a*gaussMoment a (k+1) z)
    (fun z _ => (hasDerivAt_gaussMoment a k z).hasDerivWithinAt)
    (fun z hz => by simpa only [Real.norm_eq_abs] using gaussMoment_deriv_bound ha k x z hz)
    (convex_Icc _ _) (show x ∈ Set.Icc (x-1) (x+1) from ⟨by linarith,by linarith⟩)
    (show x+h ∈ Set.Icc (x-1) (x+1) from ⟨by linarith,by linarith⟩)
  rw [Real.norm_eq_abs,Real.norm_eq_abs,add_sub_cancel_left,abs_of_pos hh] at hmv
  unfold diffMoment
  rw [abs_div,abs_of_pos hh]
  exact (div_le_iff₀ hh).mpr hmv

lemma integrable_diffMoment {a : ℝ} (ha : 0 < a) (k : ℕ) (h : ℝ) :
    Integrable (diffMoment a k h) :=
  (((integrable_gaussMoment ha k).comp_add_right h).sub
    (integrable_gaussMoment ha k)).div_const h

lemma gaussMoment_derivative_L1 {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Tendsto (fun n : ℕ => ∫ x : ℝ,
      |diffMoment a k (1/((n:ℝ)+1)) x-
        ((k:ℝ)*gaussMoment a (k-1) x-2*a*gaussMoment a (k+1) x)|)
      atTop (𝓝 0) := by
  let dg : ℝ → ℝ := fun x => (k:ℝ)*gaussMoment a (k-1) x-2*a*gaussMoment a (k+1) x
  have hdg : Integrable dg := ((integrable_gaussMoment ha (k-1)).const_mul (k:ℝ)).sub
    ((integrable_gaussMoment ha (k+1)).const_mul (2*a))
  have hstep : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝[≠] (0:ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
    exact Filter.Eventually.of_forall (fun n => by
      simp only [Set.mem_compl_iff,Set.mem_singleton_iff]
      exact ne_of_gt (by positivity))
  have hp (x : ℝ) : Tendsto (fun n : ℕ => diffMoment a k (1/((n:ℝ)+1)) x)
      atTop (𝓝 (dg x)) := by
    have hh := (hasDerivAt_gaussMoment a k x).tendsto_slope_zero.comp hstep
    simpa only [Function.comp_def,smul_eq_mul,div_eq_mul_inv,mul_comm,diffMoment,dg] using hh
  have ht := tendsto_integral_of_dominated_convergence
    (fun x => momentEnvelope a k x+|dg x|)
    (F := fun n : ℕ => fun x => |diffMoment a k (1/((n:ℝ)+1)) x-dg x|)
    (f := fun _ => (0:ℝ))
    (fun n => ((integrable_diffMoment ha k _).sub hdg).abs.aestronglyMeasurable)
    ((integrable_momentEnvelope ha k).add hdg.abs)
    (fun n => Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs,abs_abs]
      have htri : |diffMoment a k (1/((n:ℝ)+1)) x-dg x| ≤
          |diffMoment a k (1/((n:ℝ)+1)) x|+|dg x| := by
        simpa only [Real.norm_eq_abs] using
          norm_sub_le (diffMoment a k (1/((n:ℝ)+1)) x) (dg x)
      exact htri.trans (add_le_add (diffMoment_bound ha k (h := 1/((n:ℝ)+1)) (by positivity)
            (by have := (Nat.cast_nonneg n : (0:ℝ)≤n); apply (div_le_one (by positivity)).mpr; linarith) x) le_rfl)))
    (Filter.Eventually.of_forall (fun x => by simpa using ((hp x).sub_const (dg x)).abs))
  simpa only [integral_zero] using ht

lemma norm_toL1_real {f : ℝ → ℝ} (hf : Integrable f) :
    ‖hf.toL1 f‖ = ∫ x : ℝ, |f x| := by
  rw [Integrable.norm_toL1_eq_lintegral_enorm,
    ← integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable]
  simp only [Real.norm_eq_abs]

lemma momentL1_derivative {a : ℝ} (ha : 0 < a) (k : ℕ) (y : ℝ) :
    Tendsto (fun n : ℕ => ((1/((n:ℝ)+1))⁻¹) •
      (momentL1 a ha k (y+1/((n:ℝ)+1))-momentL1 a ha k y)) atTop
      (𝓝 ((k:ℝ) • momentL1 a ha (k-1) y-(2*a) • momentL1 a ha (k+1) y)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have he (n : ℕ) :
      ‖((1/((n:ℝ)+1))⁻¹) • (momentL1 a ha k (y+1/((n:ℝ)+1))-
        momentL1 a ha k y)-((k:ℝ) • momentL1 a ha (k-1) y-
          (2*a) • momentL1 a ha (k+1) y)‖ =
      ∫ x : ℝ, |diffMoment a k (1/((n:ℝ)+1)) x-
        ((k:ℝ)*gaussMoment a (k-1) x-2*a*gaussMoment a (k+1) x)| := by
    let h : ℝ := 1/((n:ℝ)+1)
    let f : ℝ → ℝ := fun x => h⁻¹ * (gaussMoment a k (x+(y+h))-
      gaussMoment a k (x+y))-
      ((k:ℝ)*gaussMoment a (k-1) (x+y)-(2*a)*gaussMoment a (k+1) (x+y))
    have hf : Integrable f :=
      ((((integrable_gaussMoment ha k).comp_add_right (y+h)).sub
        ((integrable_gaussMoment ha k).comp_add_right y)).const_mul h⁻¹).sub
      ((((integrable_gaussMoment ha (k-1)).comp_add_right y).const_mul (k:ℝ)).sub
        (((integrable_gaussMoment ha (k+1)).comp_add_right y).const_mul (2*a)))
    change ‖hf.toL1 f‖ = _
    rw [norm_toL1_real]
    have hfun : (fun x => |f x|) = fun x => |diffMoment a k h (x+y)-
        ((k:ℝ)*gaussMoment a (k-1) (x+y)-2*a*gaussMoment a (k+1) (x+y))| := by
      funext x
      simp only [f,diffMoment,add_assoc,div_eq_mul_inv,mul_comm]
    rw [hfun]
    exact integral_add_right_eq_self (fun x => |diffMoment a k h x-
      ((k:ℝ)*gaussMoment a (k-1) x-2*a*gaussMoment a (k+1) x)|) y
  simp_rw [he]
  exact gaussMoment_derivative_L1 ha k

lemma momentL1_mem_of_gaussian {a : ℝ} (ha : 0 < a)
    (S : Submodule ℝ (Lp ℝ 1 (volume : Measure ℝ))) (hS : IsClosed (S : Set (Lp ℝ 1 (volume : Measure ℝ))))
    (hbase : ∀ y, momentL1 a ha 0 y ∈ S) :
    ∀ k y, momentL1 a ha k y ∈ S := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro y
    cases k with
    | zero => exact hbase y
    | succ k =>
      have hder : (k:ℝ) • momentL1 a ha (k-1) y-
          (2*a) • momentL1 a ha (k+1) y ∈ S :=
        hS.mem_of_tendsto (momentL1_derivative ha k y)
          (Filter.Eventually.of_forall (fun n => S.smul_mem _
            (S.sub_mem (ih k (by omega) _) (ih k (by omega) _))))
      have hlow : (k:ℝ) • momentL1 a ha (k-1) y ∈ S :=
        S.smul_mem _ (ih (k-1) (by omega) y)
      have hhigh := S.sub_mem hlow hder
      rw [sub_sub_cancel] at hhigh
      have hn : (2*a) ≠ 0 := ne_of_gt (by positivity)
      have hh := S.smul_mem (2*a)⁻¹ hhigh
      simpa only [smul_smul,inv_mul_cancel₀ hn,one_smul] using hh

lemma gaussianTaylor_eq (a c : ℝ) (N : ℕ) (x : ℝ) :
    gaussianTaylor a c N x =
    (∑ k ∈ Finset.range N, (-c*x^2)^k/(Nat.factorial k : ℝ))*Real.exp (-a*x^2) := by
  unfold gaussianTaylor gaussMoment
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_pow,← pow_mul]
  ring

lemma gaussianTaylor_bound (a : ℝ) {c : ℝ} (hc : 0 ≤ c) (N : ℕ) (x : ℝ) :
    |gaussianTaylor a c N x| ≤ Real.exp (-(a-c)*x^2) := by
  rw [gaussianTaylor_eq,abs_mul,abs_of_pos (Real.exp_pos _)]
  have habs : |∑ k ∈ Finset.range N, (-c*x^2)^k/(Nat.factorial k : ℝ)| ≤
      ∑ k ∈ Finset.range N, (c*x^2)^k/(Nat.factorial k : ℝ) := by
    calc
      _ ≤ ∑ k ∈ Finset.range N, |(-c*x^2)^k/(Nat.factorial k : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        rw [abs_div,abs_pow,abs_mul,abs_neg,abs_of_nonneg hc,
          abs_of_nonneg (sq_nonneg x),abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    _ ≤ Real.exp (c*x^2)*Real.exp (-a*x^2) :=
      mul_le_mul_of_nonneg_right (habs.trans (Real.sum_le_exp_of_nonneg (by positivity) N))
        (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

lemma integrable_gaussianTaylor {a : ℝ} (ha : 0 < a) (c : ℝ) (N : ℕ) :
    Integrable (gaussianTaylor a c N) :=
  integrable_finsetSum _ (fun k _ => (integrable_gaussMoment ha (2*k)).const_mul _)

lemma gaussianTaylor_tendsto (a c x : ℝ) :
    Tendsto (fun N : ℕ => gaussianTaylor a c N x) atTop (𝓝 (gaussMoment (a+c) 0 x)) := by
  have ht := (NormedSpace.expSeries_div_hasSum_exp (-c*x^2)).tendsto_sum_nat.mul_const
    (Real.exp (-a*x^2))
  simpa only [gaussianTaylor_eq,← Real.exp_eq_exp_ℝ,← Real.exp_add,gaussMoment,pow_zero,one_mul,
    show -c*x^2+-a*x^2=-(a+c)*x^2 by ring] using ht

lemma gaussianTaylor_L1 {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) (hca : c < a) :
    Tendsto (fun N : ℕ => ∫ x : ℝ,
      |gaussianTaylor a c N x-gaussMoment (a+c) 0 x|) atTop (𝓝 0) := by
  have hp : 0 < a+c := by linarith
  have hm : 0 < a-c := by linarith
  have hh := tendsto_integral_of_dominated_convergence
    (fun x => Real.exp (-(a-c)*x^2)+Real.exp (-(a+c)*x^2))
    (F := fun N : ℕ => fun x => |gaussianTaylor a c N x-gaussMoment (a+c) 0 x|)
    (f := fun _ => (0:ℝ))
    (fun N => ((integrable_gaussianTaylor ha c N).sub (integrable_gaussMoment hp 0)).abs.aestronglyMeasurable)
    (by simpa only [Pi.add_def,gaussMoment,pow_zero,one_mul] using
      (integrable_gaussMoment hm 0).add (integrable_gaussMoment hp 0))
    (fun N => Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs,abs_abs]
      have htri := norm_sub_le (gaussianTaylor a c N x) (gaussMoment (a+c) 0 x)
      simp only [Real.norm_eq_abs,gaussMoment,pow_zero,one_mul,abs_of_pos (Real.exp_pos _)] at htri
      simpa only [gaussMoment,pow_zero,one_mul] using
        htri.trans (add_le_add (gaussianTaylor_bound a hc N x) le_rfl)))
    (Filter.Eventually.of_forall (fun x => by
      simpa using ((gaussianTaylor_tendsto a c x).sub_const (gaussMoment (a+c) 0 x)).abs))
  simpa only [integral_zero] using hh

lemma toL1_finsetSum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i, Integrable (f i)) :
    (integrable_finsetSum s (fun i _ => hf i)).toL1 (fun x => ∑ i ∈ s, f i x) =
      ∑ i ∈ s, (hf i).toL1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Integrable.toL1_zero _
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    change (((hf i).add (integrable_finsetSum s (fun j _ => hf j))).toL1
      (f i+(fun x => ∑ j ∈ s, f j x))) = _
    rw [Integrable.toL1_add _ _ (hf i)
      (integrable_finsetSum s (fun j _ => hf j)),ih]

lemma toL1_tendsto_of_integral_abs_sub {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, Integrable (f n)) (hg : Integrable g)
    (ht : Tendsto (fun n => ∫ x : ℝ, |f n x-g x|) atTop (𝓝 0)) :
    Tendsto (fun n => (hf n).toL1 (f n)) atTop (𝓝 (hg.toL1 g)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have he (n : ℕ) : ‖(hf n).toL1 (f n)-hg.toL1 g‖ = ∫ x : ℝ, |f n x-g x| := by
    change ‖((hf n).sub hg).toL1 (f n-g)‖ = _
    exact norm_toL1_real _
  simpa only [he] using ht

lemma gaussian_increment_mem {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) (hca : c < a)
    (S : Submodule ℝ (Lp ℝ 1 (volume : Measure ℝ)))
    (hS : IsClosed (S : Set (Lp ℝ 1 (volume : Measure ℝ))))
    (hbase : ∀ y, momentL1 a ha 0 y ∈ S) :
    ∀ y, momentL1 (a+c) (by linarith) 0 y ∈ S := by
  intro y
  have hm := momentL1_mem_of_gaussian ha S hS hbase
  let fp : ℕ → ℝ → ℝ := fun N x => gaussianTaylor a c N (x+y)
  have hfp (N : ℕ) : Integrable (fp N) := (integrable_gaussianTaylor ha c N).comp_add_right y
  have hin (N : ℕ) : (hfp N).toL1 (fp N) ∈ S := by
    have he : (hfp N).toL1 (fp N) =
        ∑ k ∈ Finset.range N, ((-c)^k/(Nat.factorial k:ℝ)) • momentL1 a ha (2*k) y := by
      exact toL1_finsetSum (Finset.range N)
        (fun k x => ((-c)^k/(Nat.factorial k:ℝ))*gaussMoment a (2*k) (x+y))
        (fun k => ((integrable_gaussMoment ha (2*k)).comp_add_right y).const_mul _)
    rw [he]
    exact S.sum_mem (fun k _ => S.smul_mem _ (hm _ y))
  have ht : Tendsto (fun N => ∫ x : ℝ,
      |fp N x-gaussMoment (a+c) 0 (x+y)|) atTop (𝓝 0) := by
    have he (N : ℕ) : (∫ x : ℝ, |fp N x-gaussMoment (a+c) 0 (x+y)|) =
        ∫ x : ℝ, |gaussianTaylor a c N x-gaussMoment (a+c) 0 x| :=
      integral_add_right_eq_self (fun x => |gaussianTaylor a c N x-gaussMoment (a+c) 0 x|) y
    simpa only [he] using gaussianTaylor_L1 ha hc hca
  exact hS.mem_of_tendsto (toL1_tendsto_of_integral_abs_sub hfp
    ((integrable_gaussMoment (by linarith : 0 < a+c) 0).comp_add_right y) ht)
    (Filter.Eventually.of_forall hin)

lemma gaussian_wider_precision_mem {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (S : Submodule ℝ (Lp ℝ 1 (volume : Measure ℝ)))
    (hS : IsClosed (S : Set (Lp ℝ 1 (volume : Measure ℝ))))
    (hbase : ∀ y, momentL1 a ha 0 y ∈ S) :
    ∀ y, momentL1 b (ha.trans_le hab) 0 y ∈ S := by
  obtain ⟨N,hN⟩ := exists_nat_gt ((b-a)/a+1)
  have hN0 : (0:ℝ) < N := by
    have : 0 ≤ (b-a)/a := div_nonneg (sub_nonneg.mpr hab) ha.le
    linarith
  let c : ℝ := (b-a)/N
  have hc : 0 ≤ c := div_nonneg (sub_nonneg.mpr hab) hN0.le
  have hca : c < a := by
    apply (div_lt_iff₀ hN0).mpr
    have : (b-a)/a < (N:ℝ) := by linarith
    have := (div_lt_iff₀ ha).mp this
    linarith
  have hall (n : ℕ) : ∀ y, momentL1 (a+(n:ℝ)*c) (by positivity) 0 y ∈ S := by
    induction n with
    | zero => simpa only [Nat.cast_zero,zero_mul,add_zero] using hbase
    | succ n ih =>
      have hh := gaussian_increment_mem (show 0 < a+(n:ℝ)*c by positivity) hc
        (show c < a+(n:ℝ)*c by have := mul_nonneg (Nat.cast_nonneg n) hc; linarith) S hS ih
      have he : a+(↑(n+1):ℝ)*c=(a+(n:ℝ)*c)+c := by push_cast; ring
      simpa only [he] using hh
  have he : a+(N:ℝ)*c = b := by dsimp [c]; field_simp [ne_of_gt hN0]; ring
  simpa only [he] using hall N

lemma gaussian_mem_closed_span {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (y : ℝ) :
    momentL1 b (ha.trans_le hab) 0 y ∈
      (Submodule.span ℝ (Set.range (momentL1 a ha 0))).topologicalClosure := by
  apply gaussian_wider_precision_mem ha hab _
    (Submodule.isClosed_topologicalClosure _) (fun z => ?_) y
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨z,rfl⟩)

theorem finite_gaussian_approximation {a b ε : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hε : 0 < ε) :
    ∃ (s : Finset ℝ) (c : ℝ → ℝ),
      (∫ x : ℝ, |gaussMoment b 0 x-
        ∑ y ∈ s, c y*gaussMoment a 0 (x+y)|) < ε := by
  classical
  have hm := gaussian_mem_closed_span ha hab 0
  change momentL1 b (ha.trans_le hab) 0 0 ∈
    closure (↑(Submodule.span ℝ (Set.range (momentL1 a ha 0))) : Set _) at hm
  obtain ⟨w,hw,hclose⟩ := Metric.mem_closure_iff.mp hm ε hε
  obtain ⟨c,rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hw
  refine ⟨c.support,c,?_⟩
  let f : ℝ → ℝ := fun x => ∑ y ∈ c.support, c y*gaussMoment a 0 (x+y)
  have hf : Integrable f := integrable_finsetSum _ (fun y _ =>
    ((integrable_gaussMoment ha 0).comp_add_right y).const_mul (c y))
  have hfL : hf.toL1 f = c.sum (fun y z => z • momentL1 a ha 0 y) :=
    toL1_finsetSum c.support (fun y x => c y*gaussMoment a 0 (x+y))
      (fun y => ((integrable_gaussMoment ha 0).comp_add_right y).const_mul (c y))
  rw [dist_eq_norm,← hfL] at hclose
  change ‖((((integrable_gaussMoment (ha.trans_le hab) 0).comp_add_right 0).sub hf).toL1
    (fun x => gaussMoment b 0 (x+0)-f x))‖ < ε at hclose
  rw [norm_toL1_real] at hclose
  simpa only [add_zero] using hclose

end SKRatioClock.Clock

open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Dynamics_GaussianPDFMoment
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SKRatioClock.Clock

lemma gaussianPDF_moment (v : ℝ≥0) (y x : ℝ) :
    gaussianPDFReal y v x = (Real.sqrt (2*Real.pi*v))⁻¹ *
      gaussMoment (1/(2*(v:ℝ))) 0 (x-y) := by
  unfold gaussianPDFReal gaussMoment
  simp only [pow_zero,one_mul]
  congr 2
  ring

theorem finite_gaussianPDF_approximation {v w : ℝ≥0} (hv : 0 < v) (hw : 0 < w)
    (hwv : w ≤ v) {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset ℝ) (c : ℝ → ℝ),
      (∫ x : ℝ, |gaussianPDFReal 0 w x-
        ∑ y ∈ s, c y*gaussianPDFReal (-y) v x|) < ε := by
  have hvR : (0:ℝ) < v := hv
  have hwR : (0:ℝ) < w := hw
  let kv : ℝ := (Real.sqrt (2*Real.pi*v))⁻¹
  let kw : ℝ := (Real.sqrt (2*Real.pi*w))⁻¹
  have hkv : 0 < kv := by dsimp [kv]; positivity
  have hkw : 0 < kw := by dsimp [kw]; positivity
  have hra : 0 < 1/(2*(v:ℝ)) := by positivity
  have hrab : 1/(2*(v:ℝ)) ≤ 1/(2*(w:ℝ)) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_left (show (w:ℝ) ≤ v from hwv) (by norm_num)
  obtain ⟨s,c,hc⟩ := finite_gaussian_approximation hra hrab (show 0 < ε/kw by positivity)
  refine ⟨s,fun y => kw*c y/kv,?_⟩
  have he (x : ℝ) : |gaussianPDFReal 0 w x-
      ∑ y ∈ s, (kw*c y/kv)*gaussianPDFReal (-y) v x| =
      kw*|gaussMoment (1/(2*(w:ℝ))) 0 x-
        ∑ y ∈ s, c y*gaussMoment (1/(2*(v:ℝ))) 0 (x+y)| := by
    simp only [gaussianPDF_moment,sub_zero,sub_neg_eq_add]
    change |kw*gaussMoment (1/(2*(w:ℝ))) 0 x-
      ∑ y ∈ s, (kw*c y/kv)*(kv*gaussMoment (1/(2*(v:ℝ))) 0 (x+y))| = _
    have hterm (y : ℝ) : (kw*c y/kv)*(kv*gaussMoment (1/(2*(v:ℝ))) 0 (x+y)) =
        kw*(c y*gaussMoment (1/(2*(v:ℝ))) 0 (x+y)) := by field_simp
    simp_rw [hterm]
    rw [← Finset.mul_sum,← mul_sub,abs_mul,abs_of_pos hkw]
  simp_rw [he]
  rw [integral_const_mul]
  have hh := mul_lt_mul_of_pos_left hc hkw
  rwa [mul_div_cancel₀ _ hkw.ne'] at hh

end SKRatioClock.Clock

open MeasureTheory Filter
open scoped Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Dynamics_IntegrableMulBounded
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology _root_.OAI.SKRatioGaussian.instNonemptyUnitBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology
namespace SKRatioClock.Clock

lemma integrable_mul_bounded {f u : ℝ → ℝ} {B : ℝ} (hf : Integrable f)
    (hu : AEStronglyMeasurable u) (hb : ∀ x, |u x| ≤ B) : Integrable (fun x => f x*u x) := by
  apply (hf.abs.mul_const B).mono' (hf.aestronglyMeasurable.mul hu)
  exact Filter.Eventually.of_forall (fun x => by
    simpa only [Real.norm_eq_abs,Pi.mul_apply,abs_mul] using mul_le_mul_of_nonneg_left (hb x) (abs_nonneg (f x)))

lemma pairing_abs_le {f u : ℝ → ℝ} {B : ℝ} (hf : Integrable f)
    (hu : AEStronglyMeasurable u) (hb : ∀ x, |u x| ≤ B) :
    |∫ x : ℝ, f x*u x| ≤ B*(∫ x : ℝ, |f x|) := by
  calc
    _ ≤ ∫ x : ℝ, |f x*u x| := abs_integral_le_integral_abs
    _ ≤ ∫ x : ℝ, |f x| * B := integral_mono (integrable_mul_bounded hf hu hb).abs
      (hf.abs.mul_const B) (fun x => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _))
    _ = _ := by rw [integral_mul_const]; ring

lemma pairing_sub_abs_le {f g u : ℝ → ℝ} {B : ℝ}
    (hf : Integrable f) (hg : Integrable g) (hu : AEStronglyMeasurable u)
    (hb : ∀ x, |u x| ≤ B) :
    |(∫ x : ℝ, f x*u x)-(∫ x : ℝ, g x*u x)| ≤ B*(∫ x : ℝ, |f x-g x|) := by
  rw [← integral_sub (integrable_mul_bounded hf hu hb) (integrable_mul_bounded hg hu hb)]
  simpa only [Pi.sub_apply,sub_mul] using pairing_abs_le (hf.sub hg) hu hb

lemma pairing_of_L1_limit {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {u : ℕ → ℝ → ℝ} {B : ℝ}
    (hf : ∀ᶠ n in atTop, Integrable (f n)) (hg : Integrable g)
    (hu : ∀ n, AEStronglyMeasurable (u n)) (hb : ∀ n x, |u n x| ≤ B)
    (ht : Tendsto (fun n => ∫ x : ℝ, |f n x-g x|) atTop (𝓝 0)) :
    Tendsto (fun n => (∫ x : ℝ, f n x*u n x)-(∫ x : ℝ, g x*u n x)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (by simpa using ht.const_mul B)
  filter_upwards [hf] with n hn
  simpa only [Real.norm_eq_abs] using pairing_sub_abs_le hn hg (hu n) (hb n)

theorem pairing_of_finite_approximation {ρ : ℝ → ℝ} {φ : ℝ → ℝ → ℝ}
    {u : ℕ → ℝ → ℝ} {B : ℝ}
    (hρ : Integrable ρ) (hφ : ∀ y, Integrable (φ y)) (hB : 0 < B)
    (hu : ∀ n, AEStronglyMeasurable (u n)) (hb : ∀ n x, |u n x| ≤ B)
    (ha : ∀ ε : ℝ, 0 < ε → ∃ (s : Finset ℝ) (c : ℝ → ℝ),
      (∫ x : ℝ, |ρ x-∑ y ∈ s, c y*φ y x|) < ε)
    (ht : ∀ y, Tendsto (fun n => ∫ x : ℝ, φ y x*u n x) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x : ℝ, ρ x*u n x) atTop (𝓝 0) := by
  classical
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨s,c,happrox⟩ := ha (ε/(2*B)) (by positivity)
  let F : ℝ → ℝ := fun x => ∑ y ∈ s, c y*φ y x
  have hF : Integrable F := integrable_finsetSum s (fun y _ => (hφ y).const_mul (c y))
  have hsum (n : ℕ) : (∫ x : ℝ, F x*u n x) = ∑ y ∈ s, c y*(∫ x : ℝ, φ y x*u n x) := by
    unfold F
    simp_rw [Finset.sum_mul,mul_assoc]
    rw [integral_finsetSum s (fun y _ => (integrable_mul_bounded (hφ y) (hu n) (hb n)).const_mul (c y))]
    apply Finset.sum_congr rfl
    intro y _
    simp only [integral_const_mul]
  have hconv : Tendsto (fun n => ∫ x : ℝ, F x*u n x) atTop (𝓝 0) := by
    simp_rw [hsum]
    have hh := tendsto_finsetSum s (fun y _ => (ht y).const_mul (c y))
    simpa using hh
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hconv (ε/2) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have hclose := pairing_sub_abs_le hρ hF (hu n) (hb n)
  have hh := hN n hn
  simp only [Real.dist_eq,sub_zero] at hh ⊢
  have he : B*(∫ x : ℝ, |ρ x-F x|) < ε/2 := by
    have := mul_lt_mul_of_pos_left happrox hB
    have he : B*(ε/(2*B))=ε/2 := by field_simp
    rwa [he] at this
  have htri : |∫ x : ℝ, ρ x*u n x| ≤
      |(∫ x : ℝ, ρ x*u n x)-(∫ x : ℝ, F x*u n x)|+|∫ x : ℝ, F x*u n x| := by
    simpa only [Real.norm_eq_abs] using norm_le_norm_sub_add
      (∫ x : ℝ, ρ x*u n x) (∫ x : ℝ, F x*u n x)
  linarith

end SKRatioClock.Clock

open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Dynamics_TestHistogram
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SKRatioClock.Clock

lemma measurable_stepMass (p : ℕ → ℝ) : Measurable (stepMass p) := by
  unfold stepMass
  exact Measurable.tsum (fun _ => measurable_const.indicator measurableSet_Ico)

lemma stepMass_abs_le {a : ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B) (ha : ∀ j, |a j| ≤ B)
    (x : ℝ) : |stepMass a x| ≤ B := by
  by_cases hx : 0 ≤ x
  · rw [stepMass_of_nonneg _ hx]
    exact ha _
  · rw [stepMass_of_neg _ (lt_of_not_ge hx),abs_zero]
    exact hB

lemma stepMass_mul (p a : ℕ → ℝ) (x : ℝ) :
    stepMass p x*stepMass a x=stepMass (fun j => p j*a j) x := by
  by_cases hx : 0 ≤ x
  · simp only [stepMass_of_nonneg _ hx]
  · simp only [stepMass_of_neg _ (lt_of_not_ge hx),mul_zero]

lemma summable_mul_bounded {p a : ℕ → ℝ} {B : ℝ} (hp : Summable p)
    (ha : ∀ j, |a j| ≤ B) : Summable (fun j => p j*a j) := by
  apply Summable.of_norm_bounded (hp.abs.mul_right B)
  intro j
  simpa only [Real.norm_eq_abs,abs_mul] using mul_le_mul_of_nonneg_left (ha j) (abs_nonneg (p j))

lemma integral_histogram_summable {p : ℕ → ℝ} (hp : Summable p) (q : ℝ) {n : ℕ}
    (hn : 0 < n) : ∫ x : ℝ, histogram q n p x = ∑' j, p j := by
  have hs : Real.sqrt (n:ℝ) ≠ 0 := by positivity
  unfold histogram
  rw [integral_const_mul]
  have hh : (fun x : ℝ => stepMass p (q*n+x*Real.sqrt n)) =
      (fun x : ℝ => (fun t => stepMass p (t+q*n)) (Real.sqrt n*x)) := by
    ext x
    congr 1
    ring
  rw [hh,Measure.integral_comp_mul_left (fun t : ℝ => stepMass p (t+q*n))
    (Real.sqrt (n:ℝ)),integral_add_right_eq_self,integral_stepMass hp,smul_eq_mul,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),← mul_assoc,mul_inv_cancel₀ hs,one_mul]

lemma measurable_testHistogram (q : ℝ) (n : ℕ) (a : ℕ → ℝ) :
    Measurable (testHistogram q n a) := by
  apply (measurable_stepMass a).comp
  fun_prop

lemma testHistogram_bound {a : ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B) (ha : ∀ j, |a j| ≤ B)
    (q : ℝ) (n : ℕ) (x : ℝ) : |testHistogram q n a x| ≤ B :=
  stepMass_abs_le hB ha _

lemma integral_histogram_test {p a : ℕ → ℝ} {B : ℝ} (hp : Summable p)
    (ha : ∀ j, |a j| ≤ B) (q : ℝ) {n : ℕ} (hn : 0 < n) :
    (∫ x : ℝ, histogram q n p x*testHistogram q n a x) = ∑' j, p j*a j := by
  have he (x : ℝ) : histogram q n p x*testHistogram q n a x =
      histogram q n (fun j => p j*a j) x := by
    unfold histogram testHistogram
    rw [mul_assoc,stepMass_mul]
  simp_rw [he]
  exact integral_histogram_summable (summable_mul_bounded hp ha) q hn

end SKRatioClock.Clock

open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Dynamics_PoissonBinomial
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology _root_.OAI.SKRatioGaussian.instNonemptyUnitBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SKRatioClock.Clock

theorem poisson_to_binomial {q B : ℝ} (hq : 0 < q) (hq1 : q < 1) (hB : 0 < B)
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop) (a : ℕ → ℕ → ℝ)
    (hab : ∀ n j, |a n j| ≤ B)
    (hp : ∀ y : ℝ, Tendsto (fun n => ∑' j,
      poissonMass (q*M n+y*Real.sqrt (M n)) j*a n j) atTop (𝓝 0)) :
    Tendsto (fun n => ∑' j, binomialMass q (M n) j*a n j) atTop (𝓝 0) := by
  let u : ℕ → ℝ → ℝ := fun n => testHistogram q (M n) (a n)
  have hu (n : ℕ) : AEStronglyMeasurable (u n) :=
    (measurable_testHistogram q (M n) (a n)).aestronglyMeasurable
  have hub (n : ℕ) (x : ℝ) : |u n x| ≤ B := testHistogram_bound hB.le (hab n) q (M n) x
  have hMn : ∀ᶠ n in atTop, 0 < M n := hM.eventually (eventually_gt_atTop 0)
  have hPi (y : ℝ) : ∀ᶠ n in atTop,
      Integrable (histogram q (M n) (poissonMass (q*M n+y*Real.sqrt (M n)))) := by
    filter_upwards [hMn] with n hn
    exact integrable_histogram (hasSum_poissonMass _) q hn
  have hdiff (y : ℝ) := pairing_of_L1_limit (hPi y)
    (integrable_gaussianPDFReal y ⟨q,hq.le⟩) hu hub ((poisson_density_L1 hq y).comp hM)
  have hP (y : ℝ) : Tendsto (fun n => ∫ x : ℝ,
      histogram q (M n) (poissonMass (q*M n+y*Real.sqrt (M n))) x*u n x)
      atTop (𝓝 0) := by
    apply (hp y).congr'
    filter_upwards [hMn] with n hn
    exact (integral_histogram_test (hasSum_poissonMass _).summable (hab n) q hn).symm
  have hG (y : ℝ) : Tendsto (fun n => ∫ x : ℝ, gaussianPDFReal y ⟨q,hq.le⟩ x*u n x)
      atTop (𝓝 0) := by
    have hh := (hP y).sub (hdiff y)
    simpa only [sub_sub_cancel,sub_zero] using hh
  let v : ℝ≥0 := ⟨q,hq.le⟩
  let w : ℝ≥0 := ⟨q*(1-q),mul_nonneg hq.le (by linarith)⟩
  have hv : 0 < v := hq
  have hw : 0 < w := mul_pos hq (by linarith)
  have hwv : w ≤ v := by
    change q*(1-q) ≤ q
    nlinarith [sq_nonneg q]
  have hGb : Tendsto (fun n => ∫ x : ℝ, gaussianPDFReal 0 w x*u n x)
      atTop (𝓝 0) :=
    pairing_of_finite_approximation (integrable_gaussianPDFReal 0 w)
      (fun y => integrable_gaussianPDFReal (-y) v) hB hu hub
      (fun ε hε => finite_gaussianPDF_approximation hv hw hwv hε) (fun y => hG (-y))
  have hBi : ∀ᶠ n in atTop, Integrable (histogram q (M n) (binomialMass q (M n))) := by
    filter_upwards [hMn] with n hn
    exact integrable_histogram (hasSum_binomialMass q _) q hn
  have hBd := pairing_of_L1_limit hBi (integrable_gaussianPDFReal 0 w) hu hub
    ((binomial_density_L1 hq hq1).comp hM)
  have hBin : Tendsto (fun n => ∫ x : ℝ,
      histogram q (M n) (binomialMass q (M n)) x*u n x) atTop (𝓝 0) := by
    have hh := hBd.add hGb
    simpa only [sub_add_cancel,zero_add] using hh
  apply hBin.congr'
  filter_upwards [hMn] with n hn
  exact integral_histogram_test (hasSum_binomialMass q _).summable (hab n) q hn

lemma uniform_zero_of_selections {ι : ℕ → Type*} [∀ n, Nonempty (ι n)]
    (f : (n : ℕ) → ι n → ℝ)
    (hf : ∀ i : (n : ℕ) → ι n, Tendsto (fun n => f n (i n)) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ i : ι n, |f n i| < ε := by
  classical
  intro ε hε
  let i : (n : ℕ) → ι n := fun n =>
    if h : ∃ i : ι n, ε ≤ |f n i| then Classical.choose h else Classical.choice (inferInstance : Nonempty (ι n))
  have hh : ∀ᶠ n in atTop, |f n (i n)| < ε := by
    have he := (hf i).eventually (Metric.ball_mem_nhds 0 hε)
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using he
  filter_upwards [hh] with n hn
  intro j
  by_contra h
  have hbad : ∃ j : ι n, ε ≤ |f n j| := ⟨j,le_of_not_gt h⟩
  have hlarge : ε ≤ |f n (i n)| := by simpa only [i,dite_eq_left hbad] using Classical.choose_spec hbad
  exact (not_le.mpr hn) hlarge

theorem poisson_to_binomial_bounded {q B : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop) (a : ℕ → ℕ → ℝ)
    (hab : ∀ n j, |a n j| ≤ B)
    (hp : ∀ y : ℝ, Tendsto (fun n => ∑' j,
      poissonMass (q*M n+y*Real.sqrt (M n)) j*a n j) atTop (𝓝 0)) :
    Tendsto (fun n => ∑' j, binomialMass q (M n) j*a n j) atTop (𝓝 0) := by
  apply poisson_to_binomial hq hq1 (show 0 < |B|+1 by positivity) M hM a
    (fun n j => (hab n j).trans ((le_abs_self B).trans (by linarith))) hp

theorem poisson_to_binomial_uniform_clocks {q B : ℝ} (hq : 0 < q) (hq1 : q < 1)
    {ι : ℕ → Type*} [∀ n, Nonempty (ι n)] (M : (n : ℕ) → ι n → ℕ)
    (hM : ∀ K : ℕ, ∀ᶠ n in atTop, ∀ i : ι n, K ≤ M n i)
    (a : (n : ℕ) → ι n → ℕ → ℝ) (hab : ∀ n i j, |a n i j| ≤ B)
    (hp : ∀ y ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ i : ι n,
      |∑' j, poissonMass (q*M n i+y*Real.sqrt (M n i)) j*a n i j| < ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ i : ι n,
      |∑' j, binomialMass q (M n i) j*a n i j| < ε := by
  apply uniform_zero_of_selections
  intro i
  have hMi : Tendsto (fun n => M n (i n)) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro K
    filter_upwards [hM K] with n hn
    exact hn (i n)
  apply poisson_to_binomial_bounded hq hq1 (fun n => M n (i n)) hMi (fun n => a n (i n))
    (fun n j => hab n (i n) j)
  intro y
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hp y ε hε)
  refine ⟨N,fun n hn => ?_⟩
  simpa only [Real.dist_eq,sub_zero] using hN n hn (i n)

end SKRatioClock.Clock

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Dynamics_ClockTransfer
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology _root_.OAI.SKRatioGaussian.instNonemptyUnitBall
attribute [-simp] _root_.OAI.SKRatio.Calculus.field_reversal _root_.OAI.SKRatio.Calculus.gibbsEuclideanEquiv_apply _root_.OAI.SKRatio.Calculus.lift_scalarEigenfunction _root_.OAI.SKRatio.Calculus.mass_reversal _root_.OAI.SKRatio.Calculus.reversal_reversal _root_.OAI.SKRatio.Calculus.spin_reversal _root_.OAI.SKRatio.Calculus.stationaryPairingCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap MeasureTheory Filter ProbabilityTheory SKRatioClock
namespace SKRatio.Calculus

lemma median_attempts_diverge_of_log_lower
    (G : ∀ n : ℕ, Set (Disorder n)) {c : ℝ} (hc : 0 < c)
    (hscale : ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, c*Real.log n ≤ medianTime g) :
    ∀ R : ℝ, ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, R ≤ (n:ℝ)*medianTime g := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ => (n:ℝ)*(c*Real.log n)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_atTop₀ (hlog.const_mul_atTop hc)
  intro R
  filter_upwards [hscale,hlim.eventually_ge_atTop R] with n hn hR
  intro g hg
  exact hR.trans (mul_le_mul_of_nonneg_left (hn g hg) (Nat.cast_nonneg n))

lemma upper_median_clock_diverges
    (G : ∀ n : ℕ, Set (Disorder n)) {b : ℝ} (hb : 0 < b)
    (hdiv : ∀ R : ℝ, ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, R ≤ (n:ℝ)*medianTime g) :
    ∀ K : ℕ, ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      K ≤ ⌈(1+b)*(n:ℝ)*medianTime g⌉₊ := by
  intro K
  have hp : 0 < 1+b := by linarith
  filter_upwards [hdiv ((K:ℝ)/(1+b))] with n hn
  intro g hg
  have hx := (div_le_iff₀ hp).mp (hn g hg)
  have hy : (K:ℝ) ≤ (⌈(1+b)*(n:ℝ)*medianTime g⌉₊:ℝ) := by
    apply le_trans _ (Nat.le_ceil _)
    nlinarith only [hx]
  exact_mod_cast hy

lemma upper_clock_shifted_time {n : ℕ} (hn : 0 < n) (t : ℝ)
    {b q y : ℝ} (hb : 0 < b) (hq : 0 < q)
    (hy : |y| ≤ (q*b/(2*(1+b)))*Real.sqrt (⌈(1+b)*(n:ℝ)*t⌉₊:ℝ)) :
    (1+b/2)*t ≤
      (q*(⌈(1+b)*(n:ℝ)*t⌉₊:ℝ)+y*Real.sqrt (⌈(1+b)*(n:ℝ)*t⌉₊:ℝ))/(q*n) := by
  let M : ℕ := ⌈(1+b)*(n:ℝ)*t⌉₊
  let c := q*b/(2*(1+b))
  have hc : 0 < c := by dsimp [c]; positivity
  have hcq : c < q := by
    dsimp [c]
    apply (div_lt_iff₀ (by positivity : 0 < 2*(1+b))).mpr
    nlinarith
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hM : (1+b)*(n:ℝ)*t ≤ (M:ℝ) := Nat.le_ceil _
  have hsq : Real.sqrt (M:ℝ)^2 = (M:ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have herr : -c*(M:ℝ) ≤ y*Real.sqrt (M:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hy (Real.sqrt_nonneg (M:ℝ))
    have hy' := mul_le_mul_of_nonneg_right (neg_abs_le y) (Real.sqrt_nonneg (M:ℝ))
    change |y| * Real.sqrt (M:ℝ) ≤ c*Real.sqrt (M:ℝ)*Real.sqrt (M:ℝ) at hh
    nlinarith
  apply (le_div_iff₀ (mul_pos hq hn')).mpr
  have hmain := mul_le_mul_of_nonneg_left hM (sub_pos.mpr hcq).le
  have hid : (q-c)*(1+b) = q*(1+b/2) := by
    dsimp [c]
    field_simp
    ring
  change _ ≤ q*(M:ℝ)+y*Real.sqrt (M:ℝ)
  calc
    _ = (q-c)*((1+b)*(n:ℝ)*t) := by
      calc
        _ = ((q-c)*(1+b))*(n:ℝ)*t := by rw [hid]; ring
        _ = _ := by ring
    _ ≤ (q-c)*(M:ℝ) := hmain
    _ ≤ _ := by nlinarith

lemma uniform_upper_clock_shift
    (G : ∀ n : ℕ, Set (Disorder n)) {b q : ℝ} (hb : 0 < b) (hq : 0 < q)
    (hdiv : ∀ R : ℝ, ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, R ≤ (n:ℝ)*medianTime g)
    (y : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      (1+b/2)*medianTime g ≤
        (q*(⌈(1+b)*(n:ℝ)*medianTime g⌉₊:ℝ)+
          y*Real.sqrt (⌈(1+b)*(n:ℝ)*medianTime g⌉₊:ℝ))/(q*n) := by
  have hc : 0 < q*b/(2*(1+b)) := by positivity
  have hs := (Real.tendsto_sqrt_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop)).const_mul_atTop hc
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hs.eventually_ge_atTop |y|)
  filter_upwards [upper_median_clock_diverges G hb hdiv N,eventually_gt_atTop 0] with n hn hn0
  intro g hg
  exact upper_clock_shifted_time hn0 (medianTime g) hb hq (hN _ (hn g hg))

theorem uniform_discrete_upper_of_holding
    (G : ∀ n : ℕ, Set (Disorder n)) {b q : ℝ}
    (hb : 0 < b) (hq : 0 < q) (hq1 : q < 1)
    (hdiv : ∀ R : ℝ, ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, R ≤ (n:ℝ)*medianTime g)
    (hhold : ∀ n, 0 < n → ∀ g ∈ G n, ∀ x, 1-q ≤ transition g x x)
    (hcont : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      continuousDistance g ((1+b/2)*medianTime g) ≤ δ) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      discreteDistance g ⌈(1+b)*(n:ℝ)*medianTime g⌉₊ ≤ δ := by
  classical
  let ι : ℕ → Type := fun n => Option
    ({g : Disorder n // g ∈ G n ∧ 0 < n} × Spin n ×
      {f : Observables n // ∀ x, |f x| ≤ 1})
  let M : (n : ℕ) → ι n → ℕ := fun n i => match i with
    | none => n+1
    | some j => ⌈(1+b)*(n:ℝ)*medianTime j.1.val⌉₊
  let a : (n : ℕ) → ι n → ℕ → ℝ := fun _ i k => match i with
    | none => 0
    | some j => (residualAttempt (coupling j.1.val) q ^ k) j.2.2.val j.2.1-
        FiniteLaw.mean (mass j.1.val 0) j.2.2.val
  have hM : ∀ K : ℕ, ∀ᶠ n in atTop, ∀ i : ι n, K ≤ M n i := by
    intro K
    filter_upwards [upper_median_clock_diverges G hb hdiv K,eventually_ge_atTop K] with n hn hnK
    intro i
    cases i with
    | none => exact hnK.trans (Nat.le_succ n)
    | some j => exact hn j.1.val j.1.property.1
  have hab : ∀ n (i : ι n) k, |a n i k| ≤ 2 := by
    intro n i k
    cases i with
    | none => norm_num [a]
    | some j =>
      exact residual_test_bound j.1.val hq
        (hhold n j.1.property.2 j.1.val j.1.property.1) j.2.2.val j.2.2.property j.2.1 k
  have hp : ∀ y ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ i : ι n,
      |∑' j, Clock.poissonMass (q*M n i+y*Real.sqrt (M n i)) j*a n i j| < ε := by
    intro y ε hε
    filter_upwards [uniform_upper_clock_shift G hb hq hdiv y,hcont (ε/4) (by positivity)] with n hn hcn
    intro i
    cases i with
    | none => simpa only [a,mul_zero,tsum_zero,abs_zero] using hε
    | some j =>
      change |∑' k, Clock.poissonMass
        (q*(⌈(1+b)*(n:ℝ)*medianTime j.1.val⌉₊:ℝ)+
          y*Real.sqrt (⌈(1+b)*(n:ℝ)*medianTime j.1.val⌉₊:ℝ)) k*
          ((residualAttempt (coupling j.1.val) q ^ k) j.2.2.val j.2.1-
            FiniteLaw.mean (mass j.1.val 0) j.2.2.val)| < ε
      rw [residual_poisson_test j.1.property.2 j.1.val hq.ne']
      have htime := hn j.1.val j.1.property.1
      have ht : 0 ≤ (1+b/2)*medianTime j.1.val :=
        mul_nonneg (by linarith) (medianTime_mem j.1.val).1
      have hbd := (continuous_test_bound j.1.val _ j.2.2.val j.2.2.property j.2.1).trans
        (mul_le_mul_of_nonneg_left (continuousDistance_antitone j.1.val ht htime) (by norm_num))
      have hc := hcn j.1.val j.1.property.1
      linarith
  have hbin := Clock.poisson_to_binomial_uniform_clocks hq hq1 M hM a hab hp
  intro δ hδ
  filter_upwards [hbin δ hδ,eventually_gt_atTop 0] with n hn hn0
  intro g hg
  apply Finset.sup'_le
  intro x _
  apply FiniteLaw.totalVariation_le_of_tests
  intro f hf
  let i : ι n := some (⟨g,hg,hn0⟩,x,⟨f,hf⟩)
  have hbd := hn i
  change |∑' k, Clock.binomialMass q ⌈(1+b)*(n:ℝ)*medianTime g⌉₊ k*
    ((residualAttempt (coupling g) q ^ k) f x-FiniteLaw.mean (mass g 0) f)| < δ at hbd
  rw [residual_binomial_test g hq.ne'] at hbd
  change |((transition g ^ ⌈(1+b)*(n:ℝ)*medianTime g⌉₊) *ᵥ f) x-
    FiniteLaw.mean (mass g 0) f| ≤ 2*δ
  linarith

end SKRatio.Calculus

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_FiniteChain_RatioProbabilityUniformBounds
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology _root_.OAI.SKRatioGaussian.instNonemptyUnitBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SKRatio

theorem ratio_probability_zero_of_uniform_bounds
    (law : (n : ℕ) → Measure (Disorder n))
    (G : (n : ℕ) → Set (Disorder n)) (T : (n : ℕ) → Disorder n → ℝ)
    {ε η b : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hb0 : 0 < b) (hb1 : b < 1)
    (hbase : (1 + b) / (1 - b) < 1 + η)
    (hG : Tendsto (fun n => law n (G n)ᶜ) atTop (𝓝 0))
    (hscale : ∀ A : ℝ, ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, A ≤ T n g)
    (hlower : ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      1 - ε < discreteDistance g ⌊(1 - b) * T n g⌋₊)
    (hupper : ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      discreteDistance g ⌈(1 + b) * T n g⌉₊ ≤ ε) :
    Tendsto (fun n => law n
      {g : Disorder n | 1 + η < (mixingTime g ε : ℝ) / (mixingTime g (1 - ε) : ℝ)})
      atTop (𝓝 0) := by
  have hrem : Tendsto (fun t : ℝ => 1 / ((1 - b) * t)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def, id_eq] using
      tendsto_inv_atTop_zero.comp (tendsto_id.const_mul_atTop (sub_pos.mpr hb1))
  have htail : ∀ᶠ t : ℝ in atTop,
      0 < t ∧ (1 + b) / (1 - b) + 1 / ((1 - b) * t) ≤ 1 + η := by
    filter_upwards [eventually_gt_atTop 0, hrem.eventually (gt_mem_nhds (sub_pos.mpr hbase))]
      with t ht hr
    exact ⟨ht, by linarith only [hr]⟩
  obtain ⟨A, hA⟩ := eventually_atTop.mp htail
  have hsub : ∀ᶠ n : ℕ in atTop,
      {g : Disorder n | 1 + η < (mixingTime g ε : ℝ) / (mixingTime g (1 - ε) : ℝ)} ⊆
        (G n)ᶜ := by
    filter_upwards [hscale A, hlower, hupper] with n hs hl hu
    intro g hg hgG
    obtain ⟨hT, htail⟩ := hA (T n g) (hs g hgG)
    have hratio := mixing_ratio_bound g hε0 hε1 hb0 hb1 hT (hl g hgG) (hu g hgG)
    exact not_lt_of_ge (hratio.trans htail) hg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hG
  · exact Eventually.of_forall (fun n => by positivity)
  · exact hsub.mono (fun n hn => measure_mono hn)

end SKRatio

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Dynamics_Assembly
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
attribute [-simp] _root_.OAI.SKRatio.Calculus.field_reversal _root_.OAI.SKRatio.Calculus.gibbsEuclideanEquiv_apply _root_.OAI.SKRatio.Calculus.lift_scalarEigenfunction _root_.OAI.SKRatio.Calculus.mass_reversal _root_.OAI.SKRatio.Calculus.reversal_reversal _root_.OAI.SKRatio.Calculus.spin_reversal _root_.OAI.SKRatio.Calculus.stationaryPairingCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory Filter
namespace SKRatio.Calculus

lemma uniform_holding_of_norm
    (G : ∀ n : ℕ, Set (Disorder n)) {K : ℝ} (hK : 0 < K)
    (hnorm : ∀ n, ∀ g ∈ G n,
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (coupling g)‖ ≤ K) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧
      ∀ n, 0 < n → ∀ g ∈ G n, ∀ x, 1-q ≤ transition g x x := by
  let a : ℝ := 1/(2*(1+Real.exp (2*(Real.sqrt 2*K))))
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a < 1 := by
    apply (div_lt_one (by positivity)).mpr
    linarith [Real.exp_pos (2*(Real.sqrt 2*K))]
  refine ⟨1-a,by linarith,by linarith,?_⟩
  intro n hn g hg x
  have h := attempted_holding_lower hn (coupling g) hK (hnorm n g hg) x
  rw [attemptKernel_eq_transition] at h
  simpa only [sub_sub_cancel] using h

theorem uniform_discrete_cutoff_of_positive_lag
    (G : ∀ n : ℕ, Set (Disorder n)) {c C K : ℝ} (hc : 0 < c) (hK : 0 < K)
    (hnorm : ∀ n, ∀ g ∈ G n,
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (coupling g)‖ ≤ K)
    (hscale : ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      c*Real.log n ≤ medianTime g ∧ medianTime g ≤ C*Real.log n)
    (hlag : ∀ ε α D δ : ℝ, 0 < ε → 0 < α → 0 < δ →
      ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ t : ℝ,
      0 ≤ t → t+α*Real.log n ≤ D*Real.log n →
      continuousDistance g t ≤ 1-ε → continuousDistance g (t+α*Real.log n) ≤ δ)
    {b δ : ℝ} (hb : 0 < b) (hb1 : b < 1) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      1-δ < discreteDistance g ⌊(1-b)*(n:ℝ)*medianTime g⌋₊ ∧
        discreteDistance g ⌈(1+b)*(n:ℝ)*medianTime g⌉₊ ≤ δ := by
  have hdiv := median_attempts_diverge_of_log_lower G hc
    (hscale.mono (fun _ hn g hg => (hn g hg).1))
  have hb2 : 0 < b/2 := by positivity
  have hb21 : b/2 < 1 := by linarith
  have hcont (e : ℝ) (he : 0 < e) :=
    uniform_continuous_cutoff_of_positive_lag G hc hscale hlag hb2 hb21 he
  obtain ⟨q,hq,hq1,hhold⟩ := uniform_holding_of_norm G hK hnorm
  have hup := uniform_discrete_upper_of_holding G hb hq hq1 hdiv hhold
    (fun e he => (hcont e he).mono (fun _ hn g hg => (hn g hg).2)) δ hδ
  have hlo := uniform_discrete_lower_from_continuous G hb hb1 hdiv
    (fun e he => (hcont e he).mono (fun _ hn g hg => (hn g hg).1)) δ hδ
  filter_upwards [hlo,hup] with n hnlo hnup
  intro g hg
  exact ⟨hnlo g hg,hnup g hg⟩

theorem ratio_cutoff_of_positive_lag (β ε η : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hη : 0 < η)
    (G : ∀ n : ℕ, Set (Disorder n)) {c C K : ℝ} (hc : 0 < c) (hK : 0 < K)
    (hnorm : ∀ n, ∀ g ∈ G n,
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (coupling g)‖ ≤ K)
    (hG : Tendsto (fun n => disorderLaw β n (G n)ᶜ) atTop (𝓝 0))
    (hscale : ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      c*Real.log n ≤ medianTime g ∧ medianTime g ≤ C*Real.log n)
    (hlag : ∀ ε α D δ : ℝ, 0 < ε → 0 < α → 0 < δ →
      ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ t : ℝ,
      0 ≤ t → t+α*Real.log n ≤ D*Real.log n →
      continuousDistance g t ≤ 1-ε → continuousDistance g (t+α*Real.log n) ≤ δ) :
    Tendsto
      (fun n : ℕ => disorderLaw β n
        {g : Disorder n | 1+η <
          (mixingTime g ε : ℝ)/(mixingTime g (1-ε) : ℝ)})
      atTop (𝓝 0) ∧
    (∀ᶠ n : ℕ in atTop, ∀ g : Disorder n, 0 < mixingTime g (1-ε)) := by
  refine ⟨?_,denominator_eventually_positive ε hε hε1⟩
  let b : ℝ := η/(2*(2+η))
  have hden : 0 < 2*(2+η) := by positivity
  have hb : 0 < b := div_pos hη hden
  have hb1 : b < 1 := (div_lt_one hden).mpr (by linarith)
  have hbid : b*(2+η) = η/2 := by dsimp only [b]; field_simp
  have hbase : (1+b)/(1-b) < 1+η := by
    apply (div_lt_iff₀ (sub_pos.mpr hb1)).mpr
    nlinarith only [hbid,hη]
  have hdiv := median_attempts_diverge_of_log_lower G hc
    (hscale.mono (fun _ hn g hg => (hn g hg).1))
  have hd := uniform_discrete_cutoff_of_positive_lag G hc hK hnorm hscale hlag hb hb1 hε
  apply ratio_probability_zero_of_uniform_bounds (disorderLaw β) G
    (fun n g => (n:ℝ)*medianTime g) hε hε1 hb hb1 hbase hG hdiv
  · filter_upwards [hd] with n hn
    intro g hg
    simpa only [mul_assoc] using (hn g hg).1
  · filter_upwards [hd] with n hn
    intro g hg
    simpa only [mul_assoc] using (hn g hg).2

end SKRatio.Calculus

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_UniformDrift
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory Filter
namespace SKRatio.Calculus
attribute [local instance] Classical.propDecidable

lemma replace_difference_le {n : ℕ} (f : Observables n) {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ x i, |halfDiff i f x| ≤ a) (x : Spin n) (i : Fin n) (b : Bool) :
    |f (replace x i b)-f x| ≤ 2*a := by
  by_cases hb : b = x i
  · subst b
    rw [replace_self,sub_self,abs_zero]
    positivity
  · have he : b = !(x i) := by cases hi : x i <;> cases b <;> simp_all
    rw [he]
    change |f (flip i x)-f x| ≤ 2*a
    rw [flip_sub,abs_mul,abs_mul]
    have hs : |spin x i| = 1 := by cases hi : x i <;> simp [spin,hi]
    rw [hs]
    norm_num
    linarith [h x i]

lemma oscillation_le_of_halfDiff {n : ℕ} (f : Observables n) {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ x i, |halfDiff i f x| ≤ a) (x y : Spin n) :
    |f x-f y| ≤ 2*(n:ℝ)*a := by
  have hp (k : ℕ) (hk : k ≤ n) :
      |f (updatePath x y k)-f x| ≤ 2*(k:ℝ)*a := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hk' : k < n := by omega
      have hstep := replace_difference_le f ha h (updatePath x y k) ⟨k,hk'⟩ (y ⟨k,hk'⟩)
      change |f (Function.update (updatePath x y k) ⟨k,hk'⟩ (y ⟨k,hk'⟩)) -
        f (updatePath x y k)| ≤ 2*a at hstep
      rw [←updatePath_succ x y k hk'] at hstep
      have htri := abs_sub_le (f (updatePath x y (k+1))) (f (updatePath x y k)) (f x)
      have hprev := ih (by omega)
      push_cast
      linarith
  simpa only [updatePath_end,abs_sub_comm] using hp n le_rfl

lemma halfDiff_le_sqrt_gradient {n : ℕ} (f : Observables n) {B : ℝ}
    (hB : ∀ x, unweightedGradient f x ≤ B) (x : Spin n) (i : Fin n) :
    |halfDiff i f x| ≤ Real.sqrt B := by
  have hsq : (halfDiff i f x)^2 ≤ B :=
    (Finset.single_le_sum (fun j _ => sq_nonneg (halfDiff j f x)) (Finset.mem_univ i)).trans (hB x)
  exact (Real.sqrt_sq_eq_abs _).symm ▸ Real.sqrt_le_sqrt hsq

lemma mean_difference_le_of_oscillation {n : ℕ} (g : Disorder n) (f : Observables n)
    {B : ℝ} (hosc : ∀ x y, |f x-f y| ≤ B) (x : Spin n) :
    |f x-FiniteLaw.mean (mass g 0) f| ≤ B := by
  have hid : f x-FiniteLaw.mean (mass g 0) f =
      ∑ y, mass g 0 y*(f x-f y) := by
    simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,sum_mass,one_mul,FiniteLaw.mean]
  rw [hid]
  calc
    _ ≤ ∑ y, |mass g 0 y*(f x-f y)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y, mass g 0 y*B := by
      apply Finset.sum_le_sum
      intro y _
      rw [abs_mul,abs_of_nonneg (mass_nonneg g 0 y)]
      exact mul_le_mul_of_nonneg_left (hosc x y) (mass_nonneg g 0 y)
    _ = B := by rw [←Finset.sum_mul,sum_mass,one_mul]

theorem distance_upper_of_uniform_gradient_drift {n : ℕ} (g : Disorder n) {κ t : ℝ}
    (ht : 0 ≤ t)
    (hgrad : ∀ f : Observables n, ∀ r : ℝ, ∀ y,
      deriv (fun v => unweightedGradient (semigroup (coupling g) v f) y) r -
        generator (coupling g) (unweightedGradient (semigroup (coupling g) r f)) y ≤
          -κ*unweightedGradient (semigroup (coupling g) r f) y) :
    continuousDistance g t ≤ (n:ℝ)*Real.sqrt ((n:ℝ)*Real.exp (-κ*t)) := by
  apply Finset.sup'_le
  intro x _
  apply FiniteLaw.totalVariation_le_of_tests
  intro f hf
  rw [←semigroup_eq_kernel,←gibbsMean_semigroup g t f]
  have hB (y : Spin n) : unweightedGradient (semigroup (coupling g) t f) y ≤
      (n:ℝ)*Real.exp (-κ*t) := by
    simpa only [mul_comm] using gradient_envelope_of_drift (coupling g) f ht
      (fun r _ y => hgrad f r y) (unweightedGradient_le_dim f hf) y
  have ho := oscillation_le_of_halfDiff (semigroup (coupling g) t f) (Real.sqrt_nonneg _)
    (halfDiff_le_sqrt_gradient _ hB)
  exact (mean_difference_le_of_oscillation g _ ho x).trans_eq (by ring)

theorem uniform_median_upper_of_uniform_gradient
    (G : ∀ n : ℕ, Set (Disorder n)) {κ : ℝ} (hκ : 0 < κ)
    (hgrad : ∀ n, ∀ g ∈ G n, ∀ f : Observables n, ∀ r : ℝ, ∀ y,
      deriv (fun v => unweightedGradient (semigroup (coupling g) v f) y) r -
        generator (coupling g) (unweightedGradient (semigroup (coupling g) r f)) y ≤
          -κ*unweightedGradient (semigroup (coupling g) r f) y) :
    ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, medianTime g ≤ (4/κ)*Real.log n := by
  have hlim := (dimensionDecay_tendsto_zero (by norm_num : (0:ℝ)<1)).sqrt
  simp only [Real.sqrt_zero] at hlim
  filter_upwards [eventually_gt_atTop (1:ℕ), hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))]
    with n hn hbound
  intro g hg
  have ht : 0 ≤ (4/κ)*Real.log n := by positivity
  have he : -κ*((4/κ)*Real.log n) = -(4:ℝ)*Real.log n := by field_simp
  have hid : (n:ℝ)*Real.sqrt ((n:ℝ)*Real.exp (-κ*((4/κ)*Real.log n))) =
      Real.sqrt (dimensionDecay 1 n) := by
    rw [he]
    change (n:ℝ)*Real.sqrt ((n:ℝ)*dimensionDecay 4 n) = _
    have hsq : (n:ℝ)^2*((n:ℝ)*dimensionDecay 4 n) = dimensionDecay 1 n := by
      calc
        _ = (n:ℝ)*((n:ℝ)*((n:ℝ)*dimensionDecay 4 n)) := by ring
        _ = (n:ℝ)*((n:ℝ)*dimensionDecay 3 n) := by rw [nat_mul_dimensionDecay (by omega)];norm_num
        _ = (n:ℝ)*dimensionDecay 2 n := by rw [nat_mul_dimensionDecay (by omega)];norm_num
        _ = dimensionDecay 1 n := by rw [nat_mul_dimensionDecay (by omega)];norm_num
    rw [←hsq,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (Nat.cast_nonneg _)]
  apply (medianTime_le_iff g ht).mpr
  exact (distance_upper_of_uniform_gradient_drift g ht (hgrad n g hg)).trans (hid ▸ hbound.le)

theorem ratio_cutoff_of_uniform_gradient_oai (β ε η : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hη : 0 < η)
    (G : ∀ n : ℕ, Set (Disorder n)) {κ γ K : ℝ}
    (hκ : 0 < κ) (hγ : 0 < γ) (hK : 0 < K)
    (hG : Tendsto (fun n => disorderLaw β n (G n)ᶜ) atTop (𝓝 0))
    (hnorm : ∀ n, ∀ g ∈ G n, euclideanOpNorm (coupling g) ≤ K)
    (hgap : ∀ n, ∀ g ∈ G n, ∀ f : Observables n,
      γ*FiniteLaw.variance (mass g 0) f ≤ stationaryEnergy g f)
    (hgrad : ∀ n, ∀ g ∈ G n, ∀ f : Observables n, ∀ r : ℝ, ∀ y,
      deriv (fun v => unweightedGradient (semigroup (coupling g) v f) y) r -
        generator (coupling g) (unweightedGradient (semigroup (coupling g) r f)) y ≤
          -κ*unweightedGradient (semigroup (coupling g) r f) y) :
    Tendsto
      (fun n : ℕ => disorderLaw β n
        {g : Disorder n | 1+η <
          (mixingTime g ε : ℝ)/(mixingTime g (1-ε) : ℝ)})
      atTop (𝓝 0) ∧
    (∀ᶠ n : ℕ in atTop, ∀ g : Disorder n, 0 < mixingTime g (1-ε)) := by
  let bad : ∀ n, Disorder n → Set (Spin n) := fun _ _ => ∅
  have hgp : ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ f : Observables n,
      γ*FiniteLaw.variance (mass g 0) f ≤ stationaryEnergy g f := Eventually.of_forall hgap
  have hgd (D : ℝ) (_hD : 0 < D) : ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      ∀ f : Observables n, ∀ r ∈ Set.Icc (0:ℝ) (D*Real.log n), ∀ y,
      deriv (fun v => unweightedGradient (semigroup (coupling g) v f) y) r -
        generator (coupling g) (unweightedGradient (semigroup (coupling g) r f)) y ≤
          (-κ + if y ∈ bad n g then 0 else 0)*
            unweightedGradient (semigroup (coupling g) r f) y := by
    apply Eventually.of_forall
    intro n g hg f r hr y
    simpa only [ite_self,add_zero] using hgrad n g hg f r y
  have hav (D m : ℝ) (_hD : 0 < D) (_hm : 0 < m) :
      ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ u ∈ Set.Icc (0:ℝ) (D*Real.log n), ∀ x,
      semigroup (coupling g) u (fun y => if y ∈ bad n g then 1 else 0) x ≤ dimensionDecay m n := by
    apply Eventually.of_forall
    intro n g hg u hu x
    simpa [bad,semigroup_const] using (dimensionDecay_pos m n).le
  have hrow : ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ i, ∑ j, coupling g i j ^ 2 ≤ K^2 := by
    apply Eventually.of_forall
    intro n g hg i
    exact row_squares_le_opNorm (coupling g) (coupling_symm g) hK.le (hnorm n g hg) i
  have hfields := uniform_field_tails_of_small_set G bad hκ (le_refl 0) (le_refl 0)
    hγ (sq_nonneg K) hrow hgp (by simpa only [ite_self] using hgd)
      (by simpa only [bad,Set.mem_empty_iff_false,ite_false, if_false] using hav)
  have hlag := uniform_positive_lag_of_small_set_gradient G bad hκ (le_refl 0)
    (le_refl 0) hγ hgp (by simpa only [ite_self] using hgd)
      (by simpa only [bad,Set.mem_empty_iff_false,ite_false, if_false] using hav) hfields
  have hlo := uniform_median_lower_of_small_set G bad hκ (le_refl 0) (le_refl 0) hγ hgp (by simpa only [ite_self] using hgd)
      (by simpa only [bad,Set.mem_empty_iff_false,ite_false, if_false] using hav)
  have hup := uniform_median_upper_of_uniform_gradient G hκ hgrad
  apply ratio_cutoff_of_positive_lag β ε η hε hε1 hη G (c := 1/4) (C := 4/κ)
    (by norm_num) hK hnorm hG _ hlag
  filter_upwards [hlo,hup] with n hnlo hnup
  intro g hg
  exact ⟨by simpa only [one_div_mul_eq_div] using hnlo g hg,hnup g hg⟩

end SKRatio.Calculus

end
end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Calculus.ratio_cutoff_of_uniform_gradient_oai := @OAI.SKRatio.Calculus.ratio_cutoff_of_uniform_gradient_oai

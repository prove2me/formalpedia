-- Prove2me | solution 1 for OAI.Erdos3.exists_character_centered_counting
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-16T03:26:09.325695+00:00
-- url     : https://prove2.me/submissions/70db5e5e-89c0-41e7-918b-299f1aabac41
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1323
import Theorems.Thm_OAI_Erdos3_exists_pivot_grid_bounds

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ComplexFiniteMeans
namespace OAI

section

open scoped BigOperators

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators


end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators




end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem centered_product_mean_expansion {I X : Type*} [DecidableEq I] [Fintype X]
    (S : Finset I) (hS : S.Nonempty) (F : I → X → ℝ) :
    (𝔼 x, ∏ i ∈ S, (F i x - 1)) =
      ∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card * ((𝔼 x, ∏ i ∈ S \ U, F i x) - 1) := by
  have hpoint (x : X) : (∏ i ∈ S, (F i x - 1)) =
      ∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card * (∏ i ∈ S \ U, F i x) := by
    simpa only [Finset.prod_const_one, mul_one] using
      Finset.prod_sub (fun i => F i x) (fun _ => (1 : ℝ)) S
  have hzero : (∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card) = 0 := by
    have h := (Finset.prod_sub (fun _ : I => (1 : ℝ)) (fun _ => (1 : ℝ)) S).symm
    simpa [hS.ne_empty] using h
  simp only [hpoint, Finset.expect_sum_comm, ← Finset.mul_expect]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hzero, sub_zero]

theorem centered_product_mean_abs_le {I X : Type*} [DecidableEq I] [Fintype X]
    (S : Finset I) (hS : S.Nonempty) (F : I → X → ℝ) {error : ℝ}
    (hmean : ∀ U ⊆ S, |(𝔼 x, ∏ i ∈ U, F i x) - 1| ≤ error) :
    |𝔼 x, ∏ i ∈ S, (F i x - 1)| ≤ (2 : ℝ) ^ S.card * error := by
  rw [centered_product_mean_expansion S hS F]
  calc
    _ ≤ ∑ U ∈ S.powerset,
        |(-1 : ℝ) ^ U.card * ((𝔼 x, ∏ i ∈ S \ U, F i x) - 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _U ∈ S.powerset, error := by
      apply Finset.sum_le_sum
      intro U _
      simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact hmean (S \ U) Finset.sdiff_subset
    _ = _ := by simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestComplement
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

namespace RationalFilteredNilmanifold

open Module
open scoped NNReal


section Metric


end Metric

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3

namespace RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal


end RationalFilteredNilmanifold.Niltest
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct


end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold


end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

universe u

theorem cyclic_upperComparison_mul_niltest
    {degree low N : ℕ} [NeZero N] {P R error : ℝ}
    (f g : ZMod N → ℝ) (hcompare : CyclicNiltestUpperComparison.{u} degree N P error f g)
    (hlow : low ≤ degree) (hR : 0 ≤ R)
    (hBudget : productNiltestBudget (raisedNiltestBudget R) ≤ P)
    {L₁ : Type u} [lie₁ : LieRing L₁] [alg₁ : LieAlgebra ℚ L₁] {s₁ dim₁ : ℕ}
    [top₁ : TopologicalSpace (ℝ ⊗[ℚ] L₁)] [add₁ : IsTopologicalAddGroup (ℝ ⊗[ℚ] L₁)]
    [smul₁ : ContinuousSMul ℝ (ℝ ⊗[ℚ] L₁)] [t2₁ : T2Space (ℝ ⊗[ℚ] L₁)]
    (D₁ : RationalFilteredNilmanifold L₁ s₁ dim₁) (hs₁ : s₁ ≤ degree)
    (A : D₁.Niltest (fun _ : Unit => 1)) (hA : A.UnitIntervalValued) (hAc : A.ComplexityLE R) :
    CyclicNiltestUpperComparison.{u} low N R error
      (fun x => f x * (A.evalCyclic N (fun _ => x)).re)
      (fun x => g x * (A.evalCyclic N (fun _ => x)).re) := by
  intro L₂ lie₂ alg₂ s₂ dim₂ top₂ add₂ smul₂ t2₂ D₂ hs₂ T hT hTc
  let K : Bool → Type u := BoolLieFamily L₁ L₂
  let dims : Bool → ℕ := fun b => Bool.rec dim₂ dim₁ b
  let D : ∀ b, RationalFilteredNilmanifold (K b) degree (dims b) := fun b => by
    cases b
    · exact D₂.raiseStep (hs₂.trans hlow)
    · exact D₁.raiseStep hs₁
  let U : ∀ b, (D b).Niltest (fun _ : Unit => 1) := fun b => by
    cases b
    · exact T.raiseStep (hs₂.trans hlow)
    · exact A.raiseStep hs₁
  have hUc : ∀ b, (U b).ComplexityLE (raisedNiltestBudget R) := by
    intro b
    cases b
    · exact T.raiseStep_complexity (hs₂.trans hlow) hR hTc
    · exact A.raiseStep_complexity hs₁ hR hAc
  have hU : ∀ b, (U b).UnitIntervalValued := by
    intro b
    cases b
    · exact T.raiseStep_unit_interval (hs₂.trans hlow) hT
    · exact A.raiseStep_unit_interval hs₁ hA
  have hR' : 0 ≤ raisedNiltestBudget R := hR.trans (le_raisedNiltestBudget R)
  have hcard : (Fintype.card Bool : ℝ) ≤ raisedNiltestBudget R := by
    norm_num only [Fintype.card_bool, Nat.cast_ofNat]
    unfold raisedNiltestBudget
    nlinarith [sq_nonneg (R + 2)]
  let : FiniteDimensional ℚ (∀ b, K b) :=
    (RationalFilteredNilmanifold.productFinBasis D).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ b, K b))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ b, K b)) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ b, K b)) :=
    realification_moduleTopology_t2 (RationalFilteredNilmanifold.productFinBasis D)
  let S := RationalFilteredNilmanifold.piNiltest D U hR' hcard hUc
  have hSc : S.ComplexityLE P :=
    (RationalFilteredNilmanifold.piNiltest_complexity D U hR' hcard hUc).mono hBudget
  have hSu : S.UnitIntervalValued :=
    RationalFilteredNilmanifold.piNiltest_unit_interval D U hR' hcard hUc hU
  have h := hcompare (RationalFilteredNilmanifold.pi D) le_rfl S hSu hSc
  have heval (x : ZMod N) : S.evalCyclic N (fun _ : Unit => x) =
      A.evalCyclic N (fun _ : Unit => x) * T.evalCyclic N (fun _ : Unit => x) := by
    change (RationalFilteredNilmanifold.piNiltest D U hR' hcard hUc).eval
      (fun _ : Unit => (x.val : ℤ)) = _
    rw [RationalFilteredNilmanifold.piNiltest_eval, Fintype.prod_bool]
    change (A.raiseStep hs₁).eval (fun _ : Unit => (x.val : ℤ)) *
      (T.raiseStep (hs₂.trans hlow)).eval (fun _ : Unit => (x.val : ℤ)) = _
    rw [RationalFilteredNilmanifold.Niltest.raiseStep_eval,
      RationalFilteredNilmanifold.Niltest.raiseStep_eval]
    rfl
  convert h using 1
  apply Finset.expect_congr rfl
  intro x _
  rw [heval, Complex.mul_re, (A.unit_interval_evalCyclic hA N (fun _ => x)).1,
    (T.unit_interval_evalCyclic hT N (fun _ => x)).1]
  ring

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

namespace PositiveCyclicNiltest

universe u

theorem mul_upperComparison {degree low N : ℕ} [NeZero N] {P R error : ℝ}
    {a f g : ZMod N → ℝ} (ha : PositiveCyclicNiltest.{u} degree N R a)
    (hcompare : CyclicNiltestUpperComparison.{u} degree N P error f g)
    (hlow : low ≤ degree) (hR : 0 ≤ R)
    (hBudget : productNiltestBudget (raisedNiltestBudget R) ≤ P) :
    CyclicNiltestUpperComparison.{u} low N R error
      (fun x => f x * a x) (fun x => g x * a x) := by
  rcases ha with @⟨L, lie, alg, s, dim, top, add, smul, t2, D, hs, T, hT, hTc, heval⟩
  have heq : a = fun x => (T.evalCyclic N (fun _ => x)).re := funext heval
  rw [heq]
  exact @cyclic_upperComparison_mul_niltest degree low N _ P R error
    f g @hcompare hlow hR hBudget L lie alg s dim top add smul t2 D hs T hT hTc

end PositiveCyclicNiltest
end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators NNReal

universe u

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem complement_evalCyclic (T : D.Niltest w) (N : ℕ) [NeZero N] (x : σ → ZMod N) :
    T.complement.evalCyclic N x = 1 - T.evalCyclic N x := rfl

theorem complement_unitInterval (T : D.Niltest w) (hT : T.UnitIntervalValued) :
    T.complement.UnitIntervalValued := by
  intro z
  have hz := hT z
  change (1 - T.observable z).im = 0 ∧ 0 ≤ (1 - T.observable z).re ∧
    (1 - T.observable z).re ≤ 1
  simp only [Complex.sub_im, Complex.one_im, Complex.sub_re, Complex.one_re, hz.1]
  exact ⟨by norm_num, by linarith [hz.2.2], by linarith [hz.2.1]⟩

theorem complement_complexity (T : D.Niltest w) {p : ℝ}
    (hT : T.ComplexityLE p) : T.complement.ComplexityLE (p + 1) := by
  refine ⟨hT.1.mono D (by linarith), ?_⟩
  change Real.log (2 + (1 + (T.normBound : ℝ)) + (T.lipBound : ℝ)) ≤ p + 1
  apply (Real.log_le_iff_le_exp (by positivity)).2
  rw [Real.exp_add]
  have hcap := T.observable_budget hT
  nlinarith [Real.add_one_le_exp (1 : ℝ), T.normBound.coe_nonneg, T.lipBound.coe_nonneg]

end RationalFilteredNilmanifold.Niltest

theorem PositiveCyclicNiltest.complement {degree N : ℕ} [NeZero N] {p : ℝ}
    {f : ZMod N → ℝ} (hf : PositiveCyclicNiltest.{u} degree N p f) :
    PositiveCyclicNiltest.{u} degree N (p + 1) (fun x => 1 - f x) := by
  rcases hf with ⟨D, hs, T, hT, hTc, heval⟩
  refine .of_test D hs T.complement (T.complement_unitInterval hT)
    (T.complement_complexity hTc) ?_
  intro x
  rw [T.complement_evalCyclic, Complex.sub_re, Complex.one_re, heval]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.MaskedComparisonBudget
namespace OAI

section

namespace Erdos3

theorem exists_masked_comparison_budget (a b : ℕ) {xi : ℝ} (hxi : 0 < xi) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 2 ≤ p →
      let R := (p + 2) ^ (max a b)
      (p + 2) ^ a ≤ R ∧ (p + 2) ^ b ≤ R ∧
      R + 1 ≤ (p + 2) ^ C ∧
      productNiltestBudget (raisedNiltestBudget R) ≤ (p + 2) ^ C ∧
      Real.exp (-((p + 2) ^ C)) ≤ xi := by
  obtain ⟨ell, hell⟩ := exists_nat_ge (-Real.log xi)
  let X : Polynomial ℕ := Polynomial.X
  let Y := (X + 2) ^ (max a b)
  let Q := Y + (Y + 2) ^ 2 + 3
  let E := (Q + 2) ^ 2 + Q + (Q + (Q ^ 2 + Q + 3) ^ 2) + Q ^ 2 + 4
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget (E + Y + 1 + Polynomial.C ell)
  refine ⟨C, hC, ?_⟩
  intro p hp
  dsimp only
  have hp0 : 0 ≤ p := by linarith
  have hell0 : (0 : ℝ) ≤ (ell : ℝ) := Nat.cast_nonneg ell
  have hbase : 1 ≤ p + 2 := by linarith
  have hR0 : 0 ≤ (p + 2) ^ (max a b) := pow_nonneg (by linarith) _
  have hQ0 : 0 ≤ raisedNiltestBudget ((p + 2) ^ (max a b)) :=
    hR0.trans (le_raisedNiltestBudget _)
  have hE0 : 0 ≤ productNiltestBudget (raisedNiltestBudget ((p + 2) ^ (max a b))) :=
    (sq_nonneg _).trans (productNiltestBudget_geometry hQ0)
  have hsum : productNiltestBudget (raisedNiltestBudget ((p + 2) ^ (max a b))) +
      (p + 2) ^ (max a b) + 1 + ell ≤ (p + 2) ^ C := by
    simpa [X, Y, Q, E, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbound p hp0
  have hR : (p + 2) ^ (max a b) + 1 ≤ (p + 2) ^ C := by
    linarith
  have hE : productNiltestBudget (raisedNiltestBudget ((p + 2) ^ (max a b))) ≤
      (p + 2) ^ C := by linarith
  have hellP : (ell : ℝ) ≤ (p + 2) ^ C := by linarith
  refine ⟨pow_le_pow_right₀ hbase (le_max_left _ _),
    pow_le_pow_right₀ hbase (le_max_right _ _), hR, hE, ?_⟩
  calc
    _ ≤ Real.exp (Real.log xi) := Real.exp_le_exp.mpr (by linarith)
    _ = xi := Real.exp_log hxi

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AnchoredReferenceDomination
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProbabilityWeights

theorem mean_finset_expect {X Z : Type*} [Fintype Z] (p : FiniteProbabilityWeights Z)
    (A : Finset X) (f : Z → X → ℝ) :
    p.mean (fun z => 𝔼 x ∈ A, f z x) = 𝔼 x ∈ A, p.mean (fun z => f z x) := by
  unfold mean
  simp_rw [Finset.mul_expect]
  exact (Finset.expect_sum_comm _ _ _).symm

end FiniteProbabilityWeights
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators


end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical


end Erdos3.BooleanCubeKernel

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.Energy
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem prod_mean
    {ι β : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype β] [Nonempty β]
    (F : ι → β → ℝ) :
    (∏ i, mean (F i)) =
      mean (fun y : ι → β => ∏ i, F i (y i)) := by
  classical
  simp_rw [mean, Fintype.expect_eq_sum_div_card]
  rw [Finset.prod_div_distrib, Fintype.prod_sum]
  simp

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

namespace FacePartition


end FacePartition

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators


end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CountingKernelOuter
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem countingFeature_pair (b t r u v : ℝ) :
    (𝔼 sigma : Bool, countingFeature b t sigma u * countingFeature b r sigma v) =
      1 + b * (u + v - 2) + (b ^ 2 + t * r) * (u - 1) * (v - 1) := by
  rw [Fintype.expect_eq_sum_div_card]
  norm_num [countingFeature]
  ring

theorem countingFeature_opposite {b t : ℝ} (ht : t ^ 2 = b * (1 - b)) (u v : ℝ) :
    (𝔼 sigma : Bool, countingFeature b t sigma u * countingFeature b (-t) sigma v) =
      countingKernel b u v := by
  have hc : b ^ 2 + t * (-t) = 2 * b ^ 2 - b := by nlinarith
  rw [countingFeature_pair, hc]
  rfl

theorem countingFeature_same {b t : ℝ} (ht : t ^ 2 = b * (1 - b)) (u v : ℝ) :
    (𝔼 sigma : Bool, countingFeature b t sigma u * countingFeature b t sigma v) =
      positiveCountingKernel b u v := by
  have hc : b ^ 2 + t * t = b := by nlinarith
  rw [countingFeature_pair, hc]
  unfold positiveCountingKernel
  ring

theorem countingKernel_one (u v : ℝ) : countingKernel 1 u v = u * v := by
  unfold countingKernel
  ring

theorem countingKernel_quarter (u v : ℝ) :
    countingKernel (1 / 4) u v = 3 / 8 + (3 / 8) * u + (3 / 8) * v - (1 / 8) * u * v := by
  unfold countingKernel
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem countingFeatureProduct_pair {I X Y : Type*} [Fintype I] [DecidableEq I]
    (b t r : ℝ) (f : I → X → ℝ) (g : I → Y → ℝ) (x : X) (y : Y) :
    (𝔼 sigma : I → Bool, countingFeatureProduct b t f sigma x * countingFeatureProduct b r g sigma y) =
      ∏ i, (𝔼 sigma : Bool, countingFeature b t sigma (f i x) * countingFeature b r sigma (g i y)) := by
  classical
  simp only [countingFeatureProduct, ← Finset.prod_mul_distrib]
  exact (FixedDensity.prod_mean (fun i sigma => countingFeature b t sigma (f i x) *
    countingFeature b r sigma (g i y))).symm

theorem countingFeatureProduct_mean_pair {I X Y : Type*}
    [Fintype I] [DecidableEq I] [Fintype X] [Fintype Y] (b t r : ℝ)
    (f : I → X → ℝ) (g : I → Y → ℝ) :
    (𝔼 sigma : I → Bool, (𝔼 x, countingFeatureProduct b t f sigma x) *
      (𝔼 y, countingFeatureProduct b r g sigma y)) =
      𝔼 x, 𝔼 y, ∏ i, (𝔼 sigma : Bool,
        countingFeature b t sigma (f i x) * countingFeature b r sigma (g i y)) := by
  simp_rw [Finset.expect_mul_expect]
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro x _
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro y _
  exact countingFeatureProduct_pair b t r f g x y

theorem countingKernelProductAverage_factorization {I X Y : Type*}
    [Fintype I] [DecidableEq I] [Fintype X] [Fintype Y] {b t : ℝ} (ht : t ^ 2 = b * (1 - b))
    (f : I → X → ℝ) (g : I → Y → ℝ) :
    countingKernelProductAverage b f g =
      𝔼 sigma : I → Bool, (𝔼 x, countingFeatureProduct b t f sigma x) *
        (𝔼 y, countingFeatureProduct b (-t) g sigma y) := by
  simpa only [countingFeature_opposite ht, countingKernelProductAverage] using
    (countingFeatureProduct_mean_pair b t (-t) f g).symm

theorem countingFeatureProduct_square {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]
    {b t : ℝ} (ht : t ^ 2 = b * (1 - b)) (f : I → X → ℝ) :
    (𝔼 sigma : I → Bool, (𝔼 x, countingFeatureProduct b t f sigma x) ^ 2) = positiveKernelGram b f := by
  simpa only [pow_two, countingFeature_same ht, positiveKernelGram] using
    countingFeatureProduct_mean_pair b t t f f

theorem positiveKernelGram_nonneg {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]
    {b : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) (f : I → X → ℝ) : 0 ≤ positiveKernelGram b f := by
  rw [← countingFeatureProduct_square (Real.sq_sqrt (mul_nonneg hb (sub_nonneg.mpr hb1))) f]
  exact Finset.expect_nonneg (fun _ _ => sq_nonneg _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem countingBernoulli_mean {b : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) (u : ℝ) :
    (countingBernoulli hb hb1).mean (fun sigma => if sigma then u else 1) = 1 - b + b * u := by
  simpa [FiniteProbabilityWeights.mean, countingBernoulli] using add_comm (b * u) (1 - b)

theorem countingBernoulli_product {I : Type*} [Fintype I] [DecidableEq I]
    {b : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) (u : I → ℝ) :
    (FiniteProbabilityWeights.pi (fun _ : I => countingBernoulli hb hb1)).mean
      (fun choice => ∏ i, if choice i then u i else 1) = ∏ i, (1 - b + b * u i) := by
  rw [FiniteProbabilityWeights.mean_pi_product (fun _ : I => countingBernoulli hb hb1)
    (fun i sigma => if sigma then u i else 1)]
  simp only [countingBernoulli_mean]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem countingKernelProductAverage_outer_sq_le {I X Y Z : Type*}
    [Fintype I] [DecidableEq I] [Fintype X] [Fintype Y] [Fintype Z]
    {b : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (f : Z → I → X → ℝ) (g : Z → I → Y → ℝ) :
    (𝔼 z, countingKernelProductAverage b (f z) (g z)) ^ 2 ≤
      (𝔼 z, positiveKernelGram b (f z)) * (𝔼 z, positiveKernelGram b (g z)) := by
  let t := Real.sqrt (b * (1 - b))
  have ht : t ^ 2 = b * (1 - b) := Real.sq_sqrt (mul_nonneg hb (sub_nonneg.mpr hb1))
  have hnt : (-t) ^ 2 = b * (1 - b) := by simpa only [neg_sq] using ht
  let U : Z × (I → Bool) → ℝ := fun q => 𝔼 x, countingFeatureProduct b t (f q.1) q.2 x
  let V : Z × (I → Bool) → ℝ := fun q => 𝔼 y, countingFeatureProduct b (-t) (g q.1) q.2 y
  have hleft : (𝔼 q, U q * V q) = 𝔼 z, countingKernelProductAverage b (f z) (g z) := by
    rw [expect_prod_split]
    simp only [U, V, ← countingKernelProductAverage_factorization ht]
  have hrightU : (𝔼 q, U q ^ 2) = 𝔼 z, positiveKernelGram b (f z) := by
    rw [expect_prod_split]
    simp only [U, countingFeatureProduct_square ht]
  have hrightV : (𝔼 q, V q ^ 2) = 𝔼 z, positiveKernelGram b (g z) := by
    rw [expect_prod_split]
    simp only [V, countingFeatureProduct_square hnt]
  simpa only [hleft, hrightU, hrightV] using
    Finset.expect_mul_sq_le_sq_mul_sq Finset.univ U V

theorem mean_positiveKernelGram_le_of_boolean_products {I X Z : Type*}
    [Fintype I] [DecidableEq I] [Fintype X] [Fintype Z]
    {b A : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) (f : Z → I → X → ℝ)
    (h : ∀ choice : I → Bool,
      (𝔼 z, 𝔼 x, 𝔼 y, ∏ i, if choice i then f z i x * f z i y else 1) ≤ A) :
    (𝔼 z, positiveKernelGram b (f z)) ≤ A := by
  classical
  let p := FiniteProbabilityWeights.pi (fun _ : I => countingBernoulli hb hb1)
  have hpoint (z : Z) (x y : X) : (∏ i, positiveCountingKernel b (f z i x) (f z i y)) =
      p.mean (fun choice => ∏ i, if choice i then f z i x * f z i y else 1) := by
    simpa only [positiveCountingKernel, mul_assoc] using
      (countingBernoulli_product hb hb1 (fun i => f z i x * f z i y)).symm
  calc
    (𝔼 z, positiveKernelGram b (f z)) =
        p.mean (fun choice => 𝔼 z, 𝔼 x, 𝔼 y, ∏ i, if choice i then f z i x * f z i y else 1) := by
      simp only [positiveKernelGram, hpoint, FiniteProbabilityWeights.mean_finset_expect]
    _ ≤ p.mean (fun _ => A) := p.mean_mono h
    _ = A := p.mean_const A

theorem countingKernelProductAverage_outer_abs_le {I X Y Z : Type*}
    [Fintype I] [DecidableEq I] [Fintype X] [Fintype Y] [Fintype Z]
    {b A : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) (hA : 0 ≤ A)
    (f : Z → I → X → ℝ) (g : Z → I → Y → ℝ)
    (hf : ∀ choice : I → Bool,
      (𝔼 z, 𝔼 x, 𝔼 y, ∏ i, if choice i then f z i x * f z i y else 1) ≤ A)
    (hg : ∀ choice : I → Bool,
      (𝔼 z, 𝔼 x, 𝔼 y, ∏ i, if choice i then g z i x * g z i y else 1) ≤ A) :
    |𝔼 z, countingKernelProductAverage b (f z) (g z)| ≤ A := by
  have hsq := (countingKernelProductAverage_outer_sq_le hb hb1 f g).trans
    (mul_le_mul (mean_positiveKernelGram_le_of_boolean_products hb hb1 f hf)
      (mean_positiveKernelGram_le_of_boolean_products hb hb1 g hg)
      (Finset.expect_nonneg (fun z _ => positiveKernelGram_nonneg hb hb1 (g z))) hA)
  nlinarith [sq_abs (𝔼 z, countingKernelProductAverage b (f z) (g z)),
    abs_nonneg (𝔼 z, countingKernelProductAverage b (f z) (g z))]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AxisCompression
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

end Erdos3

end

section

universe u

namespace Erdos3

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

end Erdos3

end

section

namespace Erdos3.PositiveShiftBasis

universe u

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

universe u

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

universe u

theorem CyclicNiltestUpperComparison.mono_budget
    {degree N : ℕ} [NeZero N] {P Q epsilon delta : ℝ} {f g : ZMod N → ℝ}
    (h : CyclicNiltestUpperComparison.{u} degree N Q epsilon f g)
    (hPQ : P ≤ Q) (hdelta : epsilon ≤ delta) :
    CyclicNiltestUpperComparison.{u} degree N P delta f g := by
  intro L _ _ s dim _ _ _ _ D hs T hT hcomp
  exact (h D hs T hT (hcomp.mono hPQ)).trans hdelta

namespace PositiveShiftBasis

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

end PositiveShiftBasis
end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PositiveGridFamily
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open Filter Topology

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem prod_dependent_fin_cons {j : ℕ} {X : Fin (j + 1) → Type*} [∀ i, Fintype (X i)]
    {M : Type*} [CommMonoid M] (F : (∀ i, X i) → M) :
    (∏ x, F x) = ∏ y : ∀ i : Fin j, X i.succ, ∏ a : X 0, F (Fin.cons a y) := by
  calc
    _ = ∏ p : X 0 × (∀ i : Fin j, X i.succ), F (Fin.cons p.1 p.2) := by
      apply Fintype.prod_equiv (Fin.consEquiv X).symm
      intro x
      congr 1
      simp
    _ = _ := by rw [Fintype.prod_prod_type, Finset.prod_comm]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PivotStageBoundary
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem expect_independent_product {G : Type*} [Fintype G] [Nonempty G]
    (q : ℕ) (f : G → ℝ) :
    (𝔼 t : Fin q → G, ∏ i, f (t i)) = (𝔼 x, f x) ^ q := by
  simpa [FixedDensity.mean] using (FixedDensity.prod_mean (fun _i : Fin q => f)).symm

theorem expect_common_shift_product {G : Type*} [AddGroup G] [Fintype G]
    (q : ℕ) (d : G) (f : G → ℝ) :
    (𝔼 t : Fin q → G, ∏ i, f (d + t i)) = (𝔼 x, f x) ^ q := by
  rw [expect_independent_product q (fun x => f (d + x))]
  congr 1
  apply Fintype.expect_equiv (Equiv.addLeft d)
  intro x
  rfl

theorem expect_pivot_change {R : Type*} [Ring R] [Fintype R]
    (p : R) (F : R → R → ℝ) :
    (𝔼 x, 𝔼 d, F x d) = 𝔼 w, 𝔼 d, F (w - p * d) d := by
  rw [Finset.expect_comm, Finset.expect_comm (Finset.univ : Finset R) (Finset.univ : Finset R)
    (fun w d => F (w - p * d) d)]
  apply Finset.expect_congr rfl
  intro d _
  symm
  apply Fintype.expect_equiv (Equiv.addRight (-(p * d)))
  intro w
  change F (w - p * d) d = F (w + -(p * d)) d
  rw [sub_eq_add_neg]

theorem pivot_even_moment {R : Type*} [CommRing R] [Fintype R]
    (q : ℕ) (hq : Even q) (p : R) (H : R → R → ℝ) :
    (𝔼 x, 𝔼 d, 𝔼 t : Fin q → R, ∏ i, H (x - p * t i) (d + t i)) =
      𝔼 w, |𝔼 d, H (w - p * d) d| ^ q := by
  rw [expect_pivot_change p]
  apply Finset.expect_congr rfl
  intro w _
  have hpoint (d : R) :
      (𝔼 t : Fin q → R, ∏ i, H ((w - p * d) - p * t i) (d + t i)) =
        (𝔼 a, H (w - p * a) a) ^ q := by
    have heq (t : Fin q → R) (i : Fin q) :
        H ((w - p * d) - p * t i) (d + t i) = H (w - p * (d + t i)) (d + t i) := by
      congr 1
      ring
    simp_rw [heq]
    exact expect_common_shift_product q d (fun a => H (w - p * a) a)
  simp only [hpoint, Fintype.expect_const, hq.pow_abs]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem twoSlopeMap_bijective {R : Type*} [CommRing R] (a b : R) (hab : IsUnit (b - a)) :
    Function.Bijective (fun z : R × R => (z.1 + a * z.2, z.1 + b * z.2)) := by
  obtain ⟨u, hu⟩ := hab
  constructor
  · intro x y h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    have hd : (u : R) * x.2 = (u : R) * y.2 := by
      rw [hu]
      dsimp at h1 h2
      linear_combination h2 - h1
    have hxy : x.2 = y.2 := u.isUnit.mul_left_cancel hd
    apply Prod.ext
    · dsimp at h1
      rw [hxy] at h1
      exact add_right_cancel h1
    · exact hxy
  · rintro ⟨y, z⟩
    let d := (↑(u⁻¹) : R) * (z - y)
    refine ⟨(y - a * d, d), ?_⟩
    apply Prod.ext
    · dsimp
      ring
    · change y - a * d + b * d = z
      have hd : (b - a) * d = z - y := by
        rw [← hu]
        dsimp [d]
        rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
      linear_combination hd

theorem expect_two_slopes {R : Type*} [CommRing R] [Fintype R]
    (a b : R) (hab : IsUnit (b - a)) (F : R → R → ℝ) :
    (𝔼 x, 𝔼 d, F (x + a * d) (x + b * d)) = 𝔼 y, 𝔼 z, F y z := by
  let e := Equiv.ofBijective _ (twoSlopeMap_bijective a b hab)
  have h : (𝔼 q : R × R, F (q.1 + a * q.2) (q.1 + b * q.2)) =
      𝔼 q : R × R, F q.1 q.2 := by
    apply Fintype.expect_equiv e
    intro q
    rfl
  simpa only [expect_prod_split] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem FiniteProbabilityWeights.mean_pow_two_pow_le {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (n : ℕ) (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) :
    p.mean f ^ (2 ^ n) ≤ p.mean (fun x => f x ^ (2 ^ n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = (p.mean f ^ (2 ^ n)) ^ 2 := by rw [pow_succ, pow_mul]
      _ ≤ (p.mean (fun x => f x ^ (2 ^ n))) ^ 2 :=
        pow_le_pow_left₀ (pow_nonneg (p.mean_nonneg hf) _) ih 2
      _ ≤ p.mean (fun x => (f x ^ (2 ^ n)) ^ 2) := p.mean_square_le _
      _ = _ := by simp only [pow_succ, pow_mul]

theorem weighted_dyadic_holder {X : Type*} [Fintype X] [Nonempty X]
    (n : ℕ) (D F : X → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hD : ∀ x, 0 ≤ D x) (hcap : ∀ x, D x ≤ B) :
    |𝔼 x, D x * F x| ^ (2 ^ n) ≤
      (𝔼 x, D x) ^ (2 ^ n - 1) * B * (𝔼 x, |F x| ^ (2 ^ n)) := by
  have hq : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
  have hq0 : 2 ^ n ≠ 0 := by positivity
  have hmean : 0 ≤ 𝔼 x, D x := Finset.expect_nonneg (fun x _ => hD x)
  by_cases hm : (𝔼 x, D x) = 0
  · have hsum : ∑ x, D x = 0 := by
      have h := Fintype.card_mul_expect D
      rw [hm, mul_zero] at h
      exact h.symm
    have hzero : ∀ x, D x = 0 := by
      intro x
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hD y)).mp hsum x (Finset.mem_univ x)
    simp only [hzero, zero_mul, Fintype.expect_const, abs_zero, zero_pow hq0]
    positivity
  · have hmpos : 0 < 𝔼 x, D x := lt_of_le_of_ne hmean (Ne.symm hm)
    let p := FiniteProbabilityWeights.uniform X
    have hpm : 0 < p.mean D := by simpa only [p, FiniteProbabilityWeights.uniform_mean] using hmpos
    let w := p.reweightPositive D hD hpm
    have hnorm := w.mean_pow_two_pow_le n (fun x => |F x|) (fun x => abs_nonneg _)
    have hnorm' : ((𝔼 x, D x * |F x|) / (𝔼 x, D x)) ^ (2 ^ n) ≤
        (𝔼 x, D x * |F x| ^ (2 ^ n)) / (𝔼 x, D x) := by
      simpa only [w, FiniteProbabilityWeights.reweightPositive_mean, p,
        FiniteProbabilityWeights.uniform_mean] using hnorm
    rw [div_pow] at hnorm'
    have hweighted := (div_le_iff₀ (pow_pos hmpos (2 ^ n))).mp hnorm'
    have hfactor : (𝔼 x, D x) ^ (2 ^ n) = (𝔼 x, D x) ^ (2 ^ n - 1) * (𝔼 x, D x) := by
      rw [← pow_succ, Nat.sub_add_cancel hq]
    have hpoint (x : X) : |D x * F x| = D x * |F x| := by rw [abs_mul, abs_of_nonneg (hD x)]
    have habs : |𝔼 x, D x * F x| ≤ 𝔼 x, D x * |F x| := by
      simpa only [Real.norm_eq_abs, hpoint] using
        (RCLike.norm_expect_le (K := ℝ) (f := fun x => D x * F x))
    have hmoment : (𝔼 x, D x * |F x| ^ (2 ^ n)) ≤ B * (𝔼 x, |F x| ^ (2 ^ n)) := by
      calc
        _ ≤ 𝔼 x, B * |F x| ^ (2 ^ n) :=
          Finset.expect_le_expect (fun x _ => mul_le_mul_of_nonneg_right (hcap x) (pow_nonneg (abs_nonneg _) _))
        _ = _ := (Finset.mul_expect _ _ _).symm
    calc
      _ ≤ (𝔼 x, D x * |F x|) ^ (2 ^ n) := pow_le_pow_left₀ (abs_nonneg _) habs _
      _ ≤ ((𝔼 x, D x * |F x| ^ (2 ^ n)) / (𝔼 x, D x)) * (𝔼 x, D x) ^ (2 ^ n) := hweighted
      _ = (𝔼 x, D x) ^ (2 ^ n - 1) * (𝔼 x, D x * |F x| ^ (2 ^ n)) := by
        rw [hfactor]
        field_simp [hm]
      _ ≤ (𝔼 x, D x) ^ (2 ^ n - 1) * (B * (𝔼 x, |F x| ^ (2 ^ n))) :=
        mul_le_mul_of_nonneg_left hmoment (pow_nonneg hmean _)
      _ = _ := by ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem expect_single_slope {R : Type*} [Ring R] [Fintype R] (a : R) (f : R → ℝ) :
    (𝔼 x, 𝔼 d, f (x + a * d)) = 𝔼 x, f x := by
  rw [Finset.expect_comm]
  have h (d : R) : (𝔼 x, f (x + a * d)) = 𝔼 x, f x := by
    apply Fintype.expect_equiv (Equiv.addRight (a * d))
    intro x
    rfl
  simp only [h, Fintype.expect_const]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem pivotGridFactor_root {R : Type*} [CommRing R] {l q : ℕ}
    (v : Fin l → R) (slope : R) (f : R → ℝ) (z : Fin l → Fin q → R) (x d : R) :
    pivotGridFactor v slope f z x d = pivotRootFactor v slope f z (x + slope * d) := rfl

theorem pivotRootFactor_nonneg {R : Type*} [CommRing R] {l q : ℕ}
    (v : Fin l → R) (slope : R) (f : R → ℝ) (hf : ∀ x, 0 ≤ f x)
    (z : Fin l → Fin q → R) (w : R) : 0 ≤ pivotRootFactor v slope f z w :=
  Finset.prod_nonneg (fun _ _ => hf _)

theorem pivotRootFactor_le_exp {R : Type*} [CommRing R] {l q : ℕ} {p : ℝ}
    (v : Fin l → R) (slope : R) (f : R → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ Real.exp p)
    (z : Fin l → Fin q → R) (w : R) :
    pivotRootFactor v slope f z w ≤ Real.exp ((q ^ l : ℕ) * p) := by
  calc
    _ ≤ ∏ _beta : Fin l → Fin q, Real.exp p :=
      Finset.prod_le_prod (fun beta _ => (hf _).1) (fun beta _ => (hf _).2)
    _ = _ := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        Fintype.card_fin, Real.exp_nat_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem pivot_weighted_dyadic_step {R Z : Type*} [CommRing R] [Fintype R]
    [Fintype Z] [Nonempty Z] (n : ℕ) (p : R) (D : Z → R → ℝ) (H : Z → R → R → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hD : ∀ z w, 0 ≤ D z w) (hcap : ∀ z w, D z w ≤ B) :
    |𝔼 z, 𝔼 x, 𝔼 d, D z (x + p * d) * H z x d| ^ (2 ^ (n + 1)) ≤
      (𝔼 z, 𝔼 w, D z w) ^ (2 ^ (n + 1) - 1) * B *
        (𝔼 z, 𝔼 x, 𝔼 d, 𝔼 t : Fin (2 ^ (n + 1)) → R, ∏ i, H z (x - p * t i) (d + t i)) := by
  have heven : Even (2 ^ (n + 1)) := by
    refine ⟨2 ^ n, ?_⟩
    rw [pow_succ]
    omega
  have hchange (z : Z) :
      (𝔼 x, 𝔼 d, D z (x + p * d) * H z x d) =
        𝔼 w, D z w * (𝔼 d, H z (w - p * d) d) := by
    rw [expect_pivot_change p]
    simp only [sub_add_cancel, ← Finset.mul_expect]
  let D' : Z × R → ℝ := fun u => D u.1 u.2
  let H' : Z × R → ℝ := fun u => 𝔼 d, H u.1 (u.2 - p * d) d
  have h := weighted_dyadic_holder (n + 1) D' H' hB (fun u => hD u.1 u.2) (fun u => hcap u.1 u.2)
  have hm (z : Z) := pivot_even_moment (2 ^ (n + 1)) heven p (H z)
  simpa only [D', H', expect_prod_split, hchange, hm] using h

end Erdos3

end

section

namespace Erdos3

theorem PivotCompatible.cons_erase {I R : Type*} [DecidableEq I] [CommRing R] {l : ℕ}
    {v : Fin l → R} {S : Finset I} {slopes : I → R} {a b : R}
    (h : PivotCompatible v S slopes a b) {i : I} (hi : i ∈ S) :
    PivotCompatible (Fin.cons (slopes i) v) (S.erase i) slopes a b := by
  refine ⟨h.1, ?_, ?_, ?_⟩
  · intro j hj
    exact h.2.1 j (Finset.mem_of_mem_erase hj)
  · intro j hj k hk hjk
    exact h.2.2.1 j (Finset.mem_of_mem_erase hj) k (Finset.mem_of_mem_erase hk) hjk
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · refine ⟨(h.2.1 i hi).1, (h.2.1 i hi).2, ?_⟩
      intro k hk
      exact h.2.2.1 k (Finset.mem_of_mem_erase hk) i hi (Finset.ne_of_mem_erase hk)
    · exact ⟨(h.2.2.2 j).1, (h.2.2.2 j).2.1,
        fun k hk => (h.2.2.2 j).2.2 k (Finset.mem_of_mem_erase hk)⟩

theorem pivotCompatible_zero {I R : Type*} [CommRing R]
    (v : Fin 0 → R) (S : Finset I) (slopes : I → R) (a b : R)
    (hab : IsUnit (b - a))
    (hends : ∀ i ∈ S, IsUnit (a - slopes i) ∧ IsUnit (b - slopes i))
    (hpairs : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → IsUnit (slopes i - slopes j)) :
    PivotCompatible v S slopes a b :=
  ⟨hab, hends, hpairs, fun j => Fin.elim0 j⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem pivotCellForm_cons {R : Type*} [CommRing R] {l q : ℕ}
    (v : Fin l → R) (pivot slope : R) (z : Fin l → Fin q → R) (t : Fin q → R)
    (x d : R) (i : Fin q) (beta : Fin l → Fin q) :
    pivotCellForm (Fin.cons pivot v) slope (Fin.cons t z) x d (Fin.cons i beta) =
      pivotCellForm v slope z (x - pivot * t i) (d + t i) beta := by
  simp only [pivotCellForm, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  ring

theorem pivotGridFactor_cons {R : Type*} [CommRing R] {l q : ℕ}
    (v : Fin l → R) (pivot slope : R) (f : R → ℝ) (z : Fin l → Fin q → R) (t : Fin q → R)
    (x d : R) :
    pivotGridFactor (Fin.cons pivot v) slope f (Fin.cons t z) x d =
      ∏ i : Fin q, pivotGridFactor v slope f z (x - pivot * t i) (d + t i) := by
  unfold pivotGridFactor
  rw [prod_dependent_fin_cons]
  simp only [pivotCellForm_cons]
  rw [Finset.prod_comm]

theorem pivotKernelFactor_cons {R : Type*} [CommRing R] {l q : ℕ}
    (v : Fin l → R) (pivot a b : R) (parameter : ℝ) (f g : R → ℝ)
    (z : Fin l → Fin q → R) (t : Fin q → R) (x d : R) :
    pivotKernelFactor (Fin.cons pivot v) a b parameter f g (Fin.cons t z) x d =
      ∏ i : Fin q, pivotKernelFactor v a b parameter f g z (x - pivot * t i) (d + t i) := by
  unfold pivotKernelFactor
  rw [prod_dependent_fin_cons]
  simp only [pivotCellForm_cons]
  rw [Finset.prod_comm]

theorem pivotStageIntegrand_cons {I R : Type*} [CommRing R] {l q : ℕ}
    (v : Fin l → R) (pivot : R) (S : Finset I) (slopes : I → R) (mu : I → R → ℝ)
    (a b : R) (parameter : ℝ) (f g : R → ℝ) (z : Fin l → Fin q → R) (t : Fin q → R) (x d : R) :
    pivotStageIntegrand (Fin.cons pivot v) S slopes mu a b parameter f g (Fin.cons t z) x d =
      ∏ i : Fin q, pivotStageIntegrand v S slopes mu a b parameter f g z
        (x - pivot * t i) (d + t i) := by
  simp only [pivotStageIntegrand, pivotGridFactor_cons, pivotKernelFactor_cons, Finset.prod_mul_distrib]
  rw [Finset.prod_comm]

theorem pivotStageIntegrand_peel {I R : Type*} [DecidableEq I] [CommRing R] {l q : ℕ}
    (v : Fin l → R) (S : Finset I) (slopes : I → R) (mu : I → R → ℝ)
    (a b : R) (parameter : ℝ) (f g : R → ℝ) (z : Fin l → Fin q → R) (x d : R)
    {i : I} (hi : i ∈ S) :
    pivotStageIntegrand v S slopes mu a b parameter f g z x d =
      pivotRootFactor v (slopes i) (mu i) z (x + slopes i * d) *
        pivotStageIntegrand v (S.erase i) slopes mu a b parameter f g z x d := by
  unfold pivotStageIntegrand
  rw [← Finset.mul_prod_erase S _ hi, pivotGridFactor_root]
  ring

theorem pivotStageCount_cons {I R : Type*} [CommRing R] [Fintype R] {l q : ℕ}
    (v : Fin l → R) (pivot : R) (S : Finset I) (slopes : I → R) (mu : I → R → ℝ)
    (a b : R) (parameter : ℝ) (f g : R → ℝ) :
    pivotStageCount (q := q) (Fin.cons pivot v) S slopes mu a b parameter f g =
      𝔼 z : Fin l → Fin q → R, 𝔼 x, 𝔼 d, 𝔼 t : Fin q → R,
        ∏ i : Fin q, pivotStageIntegrand v S slopes mu a b parameter f g z
          (x - pivot * t i) (d + t i) := by
  rw [pivotStageCount, expect_fin_cons]
  simp only [pivotStageIntegrand_cons]
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro z _
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro x _
  rw [Finset.expect_comm]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem pivotStageCount_step {I R : Type*} [DecidableEq I] [CommRing R] [Fintype R]
    {l : ℕ} (n : ℕ) (v : Fin l → R) (S : Finset I) (slopes : I → R) (mu : I → R → ℝ)
    (a b : R) (parameter : ℝ) (f g : R → ℝ) {i : I} (hi : i ∈ S) {p : ℝ}
    (hmu : ∀ x, 0 ≤ mu i x ∧ mu i x ≤ Real.exp p) :
    |pivotStageCount (q := 2 ^ (n + 1)) v S slopes mu a b parameter f g| ^ (2 ^ (n + 1)) ≤
      (𝔼 z : Fin l → Fin (2 ^ (n + 1)) → R, 𝔼 w, pivotRootFactor v (slopes i) (mu i) z w) ^
        (2 ^ (n + 1) - 1) * Real.exp (((2 ^ (n + 1)) ^ l : ℕ) * p) *
      pivotStageCount (q := 2 ^ (n + 1)) (Fin.cons (slopes i) v) (S.erase i) slopes mu a b parameter f g := by
  let D : (Fin l → Fin (2 ^ (n + 1)) → R) → R → ℝ := pivotRootFactor v (slopes i) (mu i)
  let H : (Fin l → Fin (2 ^ (n + 1)) → R) → R → R → ℝ :=
    pivotStageIntegrand v (S.erase i) slopes mu a b parameter f g
  have h := pivot_weighted_dyadic_step n (slopes i) D H (Real.exp_nonneg _)
    (fun z w => pivotRootFactor_nonneg v (slopes i) (mu i) (fun x => (hmu x).1) z w)
    (fun z w => pivotRootFactor_le_exp v (slopes i) (mu i) hmu z w)
  have hleft : (𝔼 z, 𝔼 x, 𝔼 d, D z (x + slopes i * d) * H z x d) =
      pivotStageCount (q := 2 ^ (n + 1)) v S slopes mu a b parameter f g := by
    unfold pivotStageCount
    apply Finset.expect_congr rfl
    intro z _
    apply Finset.expect_congr rfl
    intro x _
    apply Finset.expect_congr rfl
    intro d _
    exact (pivotStageIntegrand_peel v S slopes mu a b parameter f g z x d hi).symm
  have hright : (𝔼 z, 𝔼 x, 𝔼 d, 𝔼 t : Fin (2 ^ (n + 1)) → R,
      ∏ j, H z (x - slopes i * t j) (d + t j)) =
        pivotStageCount (q := 2 ^ (n + 1)) (Fin.cons (slopes i) v) (S.erase i) slopes mu a b parameter f g := by
    exact (pivotStageCount_cons v (slopes i) (S.erase i) slopes mu a b parameter f g).symm
  rw [hleft, hright] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem pivotGridFactor_zero {R : Type*} [CommRing R] {q : ℕ}
    (v : Fin 0 → R) (slope : R) (f : R → ℝ) (z : Fin 0 → Fin q → R) (x d : R) :
    pivotGridFactor v slope f z x d = f (x + slope * d) := by
  unfold pivotGridFactor
  rw [Fintype.prod_subsingleton _ (fun i => Fin.elim0 i)]
  simp [pivotCellForm]

theorem pivotKernelFactor_zero {R : Type*} [CommRing R] {q : ℕ}
    (v : Fin 0 → R) (a b : R) (parameter : ℝ) (f g : R → ℝ) (z : Fin 0 → Fin q → R) (x d : R) :
    pivotKernelFactor v a b parameter f g z x d = countingKernel parameter (f (x + a * d)) (g (x + b * d)) := by
  unfold pivotKernelFactor
  rw [Fintype.prod_subsingleton _ (fun i => Fin.elim0 i)]
  simp [pivotCellForm]

theorem pivotStageCount_zero {I R : Type*} [CommRing R] [Fintype R] {q : ℕ}
    (v : Fin 0 → R) (S : Finset I) (slopes : I → R) (mu : I → R → ℝ)
    (a b : R) (parameter : ℝ) (f g : R → ℝ) :
    pivotStageCount (q := q) v S slopes mu a b parameter f g =
      𝔼 x, 𝔼 d, (∏ i ∈ S, mu i (x + slopes i * d)) *
        countingKernel parameter (f (x + a * d)) (g (x + b * d)) := by
  simp only [pivotStageCount, pivotStageIntegrand, pivotGridFactor_zero,
    pivotKernelFactor_zero, Fintype.expect_const]

theorem pivotStageCount_terminal {I R : Type*} [CommRing R] [Fintype R] {l q : ℕ}
    (v : Fin l → R) (slopes : I → R) (mu : I → R → ℝ)
    (a b : R) (hab : IsUnit (b - a)) (parameter : ℝ) (f g : R → ℝ) :
    pivotStageCount (q := q) v (∅ : Finset I) slopes mu a b parameter f g =
      𝔼 z : Fin l → Fin q → R, countingKernelProductAverage parameter
        (fun (beta : Fin l → Fin q) (u : R) => f (u + ∑ j, (a - v j) * z j (beta j)))
        (fun (beta : Fin l → Fin q) (w : R) => g (w + ∑ j, (b - v j) * z j (beta j))) := by
  simp only [pivotStageCount, pivotStageIntegrand, Finset.prod_empty, one_mul]
  apply Finset.expect_congr rfl
  intro z _
  exact expect_two_slopes a b hab (fun u w => ∏ beta : Fin l → Fin q,
    countingKernel parameter (f (u + ∑ j, (a - v j) * z j (beta j)))
      (g (w + ∑ j, (b - v j) * z j (beta j))))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PivotNativeIteration
namespace OAI

section

namespace Erdos3

theorem pivotIterationBound_nonneg (q r m : ℕ) (p : ℝ) {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ pivotIterationBound q r m p B :=
  mul_nonneg (Real.exp_nonneg _) (pow_nonneg hB _)

theorem pivotIterationBound_zero (q m : ℕ) (p B : ℝ) :
    pivotIterationBound q 0 m p B = B ^ (2 * m) := by
  simp [pivotIterationBound]

theorem pivotIterationBound_step {q : ℕ} (hq : 1 ≤ q) (r m : ℕ) (p : ℝ)
    {B : ℝ} (hB : 1 ≤ B) :
    (B ^ m) ^ (q - 1) * Real.exp ((m : ℝ) * p) *
        pivotIterationBound q r (q * m) p B ≤
      (pivotIterationBound q (r + 1) m p B) ^ q := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have he : (m : ℝ) * p + r * p * (q * m) / q =
      q * (((r + 1 : ℕ) : ℝ) * p * m / q) := by
    push_cast
    field_simp [hq0]
    ring
  have hn : m * (q - 1) + (r + 2) * (q * m) ≤ ((r + 1 + 2) * m) * q := by
    have hsub : q - 1 + 1 = q := Nat.sub_add_cancel hq
    nlinarith
  unfold pivotIterationBound
  simp only [Nat.cast_mul]
  rw [mul_pow, ← Real.exp_nat_mul]
  calc
    (B ^ m) ^ (q - 1) * Real.exp ((m : ℝ) * p) *
        (Real.exp ((r : ℝ) * p * (q * m) / q) * B ^ ((r + 2) * (q * m))) =
      (Real.exp ((m : ℝ) * p) * Real.exp ((r : ℝ) * p * (q * m) / q)) *
        ((B ^ m) ^ (q - 1) * B ^ ((r + 2) * (q * m))) := by ring
    _ = Real.exp (q * (((r + 1 : ℕ) : ℝ) * p * m / q)) *
        B ^ (m * (q - 1) + (r + 2) * (q * m)) := by
      rw [← Real.exp_add, he, ← pow_mul, ← pow_add]
    _ ≤ Real.exp (q * (((r + 1 : ℕ) : ℝ) * p * m / q)) *
        B ^ (((r + 1 + 2) * m) * q) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB hn) (Real.exp_nonneg _)
    _ = _ := by rw [pow_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem pivotStageCount_terminal_le {I R : Type*} [CommRing R] [Fintype R]
    {l q : ℕ} (v : Fin l → R) (slopes : I → R) (mu : I → R → ℝ)
    (a b : R) (hab : IsUnit (b - a)) {parameter A : ℝ}
    (hparameter : 0 ≤ parameter) (hparameter1 : parameter ≤ 1) (hA : 0 ≤ A)
    (f g : R → ℝ)
    (hf : ∀ choice : (Fin l → Fin q) → Bool,
      (𝔼 z : Fin l → Fin q → R, 𝔼 u, 𝔼 w, ∏ beta : Fin l → Fin q,
        if choice beta then
          f (u + ∑ j, (a - v j) * z j (beta j)) *
          f (w + ∑ j, (a - v j) * z j (beta j)) else 1) ≤ A)
    (hg : ∀ choice : (Fin l → Fin q) → Bool,
      (𝔼 z : Fin l → Fin q → R, 𝔼 u, 𝔼 w, ∏ beta : Fin l → Fin q,
        if choice beta then
          g (u + ∑ j, (b - v j) * z j (beta j)) *
          g (w + ∑ j, (b - v j) * z j (beta j)) else 1) ≤ A) :
    |pivotStageCount (q := q) v (∅ : Finset I) slopes mu a b parameter f g| ≤ A := by
  rw [pivotStageCount_terminal v slopes mu a b hab]
  exact countingKernelProductAverage_outer_abs_le hparameter hparameter1 hA _ _ hf hg

theorem pivotStageCount_iterate {I R : Type*} [DecidableEq I] [CommRing R] [Fintype R]
    (s n : ℕ) (slopes : I → R) (mu : I → R → ℝ)
    (a b : R) (parameter : ℝ) (f g : R → ℝ) {p B : ℝ} (hB : 1 ≤ B)
    (hmu : ∀ i x, 0 ≤ mu i x ∧ mu i x ≤ Real.exp p)
    (hroot : ∀ {l : ℕ}, l ≤ s → ∀ (v : Fin l → R) (i : I),
      (∀ j, IsUnit (slopes i - v j)) →
      (𝔼 z : Fin l → Fin (2 ^ (n + 1)) → R, 𝔼 w,
        pivotRootFactor v (slopes i) (mu i) z w) ≤ B ^ ((2 ^ (n + 1)) ^ l))
    (hterminal : ∀ {l : ℕ}, l ≤ s → ∀ (v : Fin l → R),
      PivotCompatible v (∅ : Finset I) slopes a b →
      |pivotStageCount (q := 2 ^ (n + 1)) v (∅ : Finset I) slopes mu a b parameter f g| ≤
        B ^ (2 * (2 ^ (n + 1)) ^ l))
    {l : ℕ} (v : Fin l → R) (S : Finset I) (hsize : l + S.card ≤ s)
    (hcompatible : PivotCompatible v S slopes a b) :
    |pivotStageCount (q := 2 ^ (n + 1)) v S slopes mu a b parameter f g| ≤
      pivotIterationBound (2 ^ (n + 1)) S.card ((2 ^ (n + 1)) ^ l) p B := by
  have hq : 1 ≤ 2 ^ (n + 1) := Nat.one_le_pow (n + 1) 2 (by omega)
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  induction S using Finset.induction_on generalizing l with
  | empty =>
      simpa only [Finset.card_empty, pivotIterationBound_zero] using
        hterminal (by simpa only [Finset.card_empty, add_zero] using hsize) v hcompatible
  | @insert i S hi ih =>
      have hmem : i ∈ insert i S := Finset.mem_insert_self i S
      have hc := hcompatible.cons_erase hmem
      rw [Finset.erase_insert hi] at hc
      have hs : (l + 1) + S.card ≤ s := by
        rw [Finset.card_insert_of_notMem hi] at hsize
        omega
      have hn := ih (Fin.cons (slopes i) v) hs hc
      have hrep : (2 ^ (n + 1)) ^ (l + 1) = 2 ^ (n + 1) * (2 ^ (n + 1)) ^ l := by
        rw [pow_succ, Nat.mul_comm]
      rw [hrep] at hn
      have hr := pivotStageCount_step n v (insert i S) slopes mu a b parameter f g hmem (hmu i)
      rw [Finset.erase_insert hi] at hr
      have hd := hroot (show l ≤ s by omega) v i
        (fun j => (hcompatible.2.2.2 j).2.2 i hmem)
      have hd0 : 0 ≤ (𝔼 z : Fin l → Fin (2 ^ (n + 1)) → R, 𝔼 w,
          pivotRootFactor v (slopes i) (mu i) z w) :=
        Finset.expect_nonneg (fun z _ => Finset.expect_nonneg
          (fun w _ => pivotRootFactor_nonneg v (slopes i) (mu i) (fun x => (hmu i x).1) z w))
      have hcoef := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hd0 hd (2 ^ (n + 1) - 1))
        (Real.exp_nonneg (((2 ^ (n + 1)) ^ l : ℕ) * p))
      have hcoef0 : 0 ≤ (𝔼 z : Fin l → Fin (2 ^ (n + 1)) → R, 𝔼 w,
          pivotRootFactor v (slopes i) (mu i) z w) ^ (2 ^ (n + 1) - 1) *
          Real.exp (((2 ^ (n + 1)) ^ l : ℕ) * p) :=
        mul_nonneg (pow_nonneg hd0 _) (Real.exp_nonneg _)
      have hpower := hr.trans ((mul_le_mul_of_nonneg_left (le_abs_self _) hcoef0).trans
        (mul_le_mul hcoef hn (abs_nonneg _)
          (mul_nonneg (pow_nonneg (pow_nonneg hB0 _) _) (Real.exp_nonneg _))))
      have hfinal := hpower.trans
        (pivotIterationBound_step hq S.card ((2 ^ (n + 1)) ^ l) p hB)
      rw [Finset.card_insert_of_notMem hi]
      exact le_of_pow_le_pow_left₀ (by omega)
        (pivotIterationBound_nonneg _ _ _ _ hB0) hfinal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_pivot_stage_bound (s : ℕ) {delta C0 : ℝ} (hdelta : 0 < delta) (hC0 : 1 ≤ C0) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi0 : ℝ, 0 < xi0 ∧
    ∀ {N : ℕ} [NeZero N] {p xi : ℝ}, 2 ≤ p → 0 < xi → xi ≤ xi0 →
      Odd N → Real.exp ((p + 2) ^ C) ≤ N →
      ∀ n : ℕ, ((2 ^ (n + 1) : ℕ) : ℝ) ≤ C0 * p →
      ∀ {I : Type} [DecidableEq I] (slopes : I → ZMod N) (mu : I → ZMod N → ℝ)
        (a b : ZMod N) (parameter : ℝ) (f g : ZMod N → ℝ),
      0 ≤ parameter → parameter ≤ 1 →
      (∀ i x, 0 ≤ mu i x ∧ mu i x ≤ Real.exp p) →
      (∀ i, CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) (mu i) (fun _ => 1 + xi)) →
      (∀ x, 0 ≤ f x ∧ f x ≤ Real.exp p) →
      CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) f (fun _ => 1 + xi) →
      (∀ x, 0 ≤ g x ∧ g x ≤ Real.exp p) →
      CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) g (fun _ => 1 + xi) →
      ∀ {l : ℕ} (v : Fin l → ZMod N) (S : Finset I), l + S.card ≤ s →
        PivotCompatible v S slopes a b →
        |pivotStageCount (q := 2 ^ (n + 1)) v S slopes mu a b parameter f g| ≤
          pivotIterationBound (2 ^ (n + 1)) S.card ((2 ^ (n + 1)) ^ l) p (1 + delta) := by
  obtain ⟨C, hC, xi0, hxi0, hgrid⟩ := exists_pivot_grid_bounds s hdelta hC0
  refine ⟨C, hC, xi0, hxi0, ?_⟩
  intro N _ p xi hp hxi hxib hodd hN n hqcap I _ slopes mu a b parameter f g
    hparameter hparameter1 hmu hcompare hf hfcompare hg hgcompare l v S hsize hcompatible
  have hq : 1 ≤ 2 ^ (n + 1) := Nat.one_le_pow (n + 1) 2 (by omega)
  have hB0 : 0 ≤ 1 + delta := by linarith
  apply pivotStageCount_iterate s n slopes mu a b parameter f g (by linarith) hmu
    (hroot := ?_) (hterminal := ?_) v S hsize hcompatible
  · intro k hk u i hunit
    exact (hgrid hp hxi hxib hodd hN hk hq hqcap u (slopes i) hunit (mu i)
      (hmu i) (@hcompare i)).1
  · intro k hk u hc
    apply pivotStageCount_terminal_le u slopes mu a b hc.1 hparameter hparameter1
      (pow_nonneg hB0 _) f g
    · exact (hgrid hp hxi hxib hodd hN hk hq hqcap u a
        (fun j => (hc.2.2.2 j).1) f hf hfcompare).2
    · exact (hgrid hp hxi hxib hodd hN hk hq hqcap u b
        (fun j => (hc.2.2.2 j).2.1) g hg hgcompare).2

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ComplexPositiveMasks
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem complexMaskComponent_abs_le (b : Bool) (z : ℂ) :
    |complexMaskComponent b z| ≤ ‖z‖ := by
  cases b
  · exact Complex.abs_im_le_norm z
  · exact Complex.abs_re_le_norm z

theorem complexPositiveMask_bounds (t : Bool × Bool) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    0 ≤ complexPositiveMask t z ∧ complexPositiveMask t z ≤ 1 := by
  have hs : |complexMaskSign t.2| = 1 := by cases t.2 <;> norm_num [complexMaskSign]
  have h : |complexMaskSign t.2 * complexMaskComponent t.1 z| ≤ 1 := by
    rw [abs_mul, hs, one_mul]
    exact (complexMaskComponent_abs_le t.1 z).trans hz
  obtain ⟨hl, hu⟩ := abs_le.mp h
  dsimp [complexPositiveMask]
  constructor <;> linarith

theorem complexPositiveMask_lipschitz (t : Bool × Bool) :
    LipschitzWith 1 (complexPositiveMask t) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have hs : |complexMaskSign t.2| = 1 := by cases t.2 <;> norm_num [complexMaskSign]
  have hc : complexMaskComponent t.1 (z - w) =
      complexMaskComponent t.1 z - complexMaskComponent t.1 w := by
    cases t.1 <;> rfl
  have he : complexPositiveMask t z - complexPositiveMask t w =
      complexMaskSign t.2 * complexMaskComponent t.1 (z - w) / 2 := by
    rw [hc]
    dsimp [complexPositiveMask]
    ring
  rw [NNReal.coe_one, one_mul, Real.dist_eq, he, abs_div, abs_mul, hs, one_mul]
  norm_num only [show |(2 : ℝ)| = 2 by norm_num]
  rw [dist_eq_norm]
  linarith [complexMaskComponent_abs_le t.1 (z - w), norm_nonneg (z - w)]

theorem complexMaskCoefficient_norm (t : Bool × Bool) : ‖complexMaskCoefficient t‖ = 1 := by
  rcases t with ⟨b, c⟩
  cases b <;> cases c <;> norm_num [complexMaskCoefficient, complexMaskSign]

theorem complexPositiveMask_expansion (z : ℂ) :
    z = ∑ t : Bool × Bool, complexMaskCoefficient t * (complexPositiveMask t z : ℂ) := by
  apply Complex.ext <;>
    simp [Fintype.sum_prod_type, complexMaskCoefficient,
      complexPositiveMask, complexMaskSign, complexMaskComponent] <;> ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CountingDeficitDetection
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem countingKernelAverage_one {X : Type*} [Fintype X] (w f g : X → ℝ) :
    countingKernelAverage 1 w f g = 𝔼 x, w x * f x * g x := by
  simp only [countingKernelAverage, countingKernel_one, mul_assoc]

theorem countingKernelAverage_quarter {X : Type*} [Fintype X] (w f g : X → ℝ) :
    countingKernelAverage (1 / 4) w f g =
      (3 / 8) * (𝔼 x, w x) + (3 / 8) * (𝔼 x, w x * f x) +
      (3 / 8) * (𝔼 x, w x * g x) - (1 / 8) * (𝔼 x, w x * f x * g x) := by
  have hpoint (x) : w x * countingKernel (1 / 4) (f x) (g x) =
      (3 / 8) * w x + (3 / 8) * (w x * f x) +
      (3 / 8) * (w x * g x) - (1 / 8) * (w x * f x * g x) := by
    rw [countingKernel_quarter]
    ring
  simp only [countingKernelAverage, hpoint, Finset.expect_add_distrib,
    Finset.expect_sub_distrib, ← Finset.mul_expect]

theorem quarterKernel_deficit_surplus {A00 A10 A01 A11 tau : ℝ}
    (h00 : |A00 - 1| ≤ tau / 18) (h10 : |A10 - 1| ≤ tau / 18)
    (h01 : |A01 - 1| ≤ tau / 18) (h11 : A11 < 1 - tau) :
    1 + tau / 16 < (3 / 8) * A00 + (3 / 8) * A10 + (3 / 8) * A01 - (1 / 8) * A11 := by
  obtain ⟨h00l, _⟩ := abs_le.mp h00
  obtain ⟨h10l, _⟩ := abs_le.mp h10
  obtain ⟨h01l, _⟩ := abs_le.mp h01
  linarith

theorem exists_countingKernel_surplus {X : Type*} [Fintype X] {tau : ℝ} (htau : 0 < tau)
    (w f g : X → ℝ) (h00 : |(𝔼 x, w x) - 1| ≤ tau / 18)
    (h10 : |(𝔼 x, w x * f x) - 1| ≤ tau / 18)
    (h01 : |(𝔼 x, w x * g x) - 1| ≤ tau / 18)
    (hbad : tau < |(𝔼 x, w x * f x * g x) - 1|) :
    ∃ b : ℝ, (b = 1 ∨ b = 1 / 4) ∧ 1 + tau / 16 < countingKernelAverage b w f g := by
  rcases lt_abs.mp hbad with hsurplus | hdeficit
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [countingKernelAverage_one]
    linarith
  · refine ⟨1 / 4, Or.inr rfl, ?_⟩
    rw [countingKernelAverage_quarter]
    exact quarterKernel_deficit_surplus h00 h10 h01 (by linarith)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DyadicCountingParameters
namespace OAI

section

namespace Erdos3

open Filter Topology

theorem exists_counting_kernel_parameters (s : ℕ) {tau : ℝ} (htau : 0 < tau) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ C0 : ℝ, 1 ≤ C0 ∧
      ∀ p : ℝ, 2 ≤ p → ∃ n : ℕ, ((2 ^ (n + 1) : ℕ) : ℝ) ≤ C0 * p ∧
        ∀ r : ℕ, r ≤ s →
          pivotIterationBound (2 ^ (n + 1)) r 1 p (1 + delta) < 1 + tau := by
  have hcontinuous : ContinuousAt
      (fun x : ℝ => Real.exp ((s : ℝ) * x) * (1 + x) ^ (s + 2)) 0 := by fun_prop
  have htend : Tendsto (fun x : ℝ => Real.exp ((s : ℝ) * x) * (1 + x) ^ (s + 2))
      (𝓝 0) (𝓝 1) := by simpa using hcontinuous.tendsto
  have heventually : ∀ᶠ x : ℝ in 𝓝 0,
      Real.exp ((s : ℝ) * x) * (1 + x) ^ (s + 2) < 1 + tau :=
    htend.eventually_lt_const (by linarith)
  obtain ⟨a, ha, hball⟩ := Metric.eventually_nhds_iff_ball.mp heventually
  let delta := min a 1 / 2
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hdelta1 : delta < 1 := by
    dsimp [delta]
    have h := min_le_right a (1 : ℝ)
    linarith
  have hdeltaa : delta < a := by
    dsimp [delta]
    have h := min_le_left a (1 : ℝ)
    linarith
  have hsmall : Real.exp ((s : ℝ) * delta) * (1 + delta) ^ (s + 2) < 1 + tau :=
    hball delta (by simpa [Real.dist_eq, abs_of_pos hdelta] using hdeltaa)
  refine ⟨delta, hdelta, 2 / delta, ?_, ?_⟩
  · apply (le_div_iff₀ hdelta).2
    linarith
  · intro p hp
    have hp0 : 0 < p := by linarith
    have hnear : 1 ≤ p / delta := by
      apply (le_div_iff₀ hdelta).2
      linarith
    obtain ⟨n, hlo, hhi⟩ := exists_nat_pow_near hnear (show (1 : ℝ) < 2 by norm_num)
    have hq0 : 0 < ((2 ^ (n + 1) : ℕ) : ℝ) := by positivity
    have hqcap : ((2 ^ (n + 1) : ℕ) : ℝ) ≤ (2 / delta) * p := by
      rw [Nat.cast_pow, Nat.cast_ofNat, pow_succ]
      calc
        (2 : ℝ) ^ n * 2 ≤ (p / delta) * 2 := mul_le_mul_of_nonneg_right hlo (by norm_num)
        _ = _ := by ring
    have hpq : p / ((2 ^ (n + 1) : ℕ) : ℝ) ≤ delta := by
      apply (div_le_iff₀ hq0).2
      have hhi' : p / delta < ((2 ^ (n + 1) : ℕ) : ℝ) := by
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using hhi
      have h := (div_lt_iff₀ hdelta).mp hhi'
      nlinarith
    refine ⟨n, hqcap, ?_⟩
    intro r hrs
    have hexp : (r : ℝ) * p / ((2 ^ (n + 1) : ℕ) : ℝ) ≤ s * delta := by
      rw [mul_div_assoc]
      exact mul_le_mul (by exact_mod_cast hrs) hpq (le_of_lt (div_pos hp0 hq0))
        (Nat.cast_nonneg s)
    have hpow : (1 + delta) ^ (r + 2) ≤ (1 + delta) ^ (s + 2) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    unfold pivotIterationBound
    simp only [Nat.cast_one, mul_one]
    exact (mul_le_mul (Real.exp_le_exp.mpr hexp) hpow
      (pow_nonneg (by linarith) _) (Real.exp_nonneg _)).trans_lt hsmall

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteProductSumEstimate
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem norm_expect_product_sum_le {I J X : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [Fintype X]
    (c : I → J → ℂ) (A : I → J → X → ℂ) {error : ℝ}
    (hc : ∀ i j, ‖c i j‖ = 1)
    (hA : ∀ choice : I → J, ‖𝔼 x, ∏ i, A i (choice i) x‖ ≤ error) :
    ‖𝔼 x, ∏ i, ∑ j, c i j * A i j x‖ ≤ (Fintype.card J : ℝ) ^ Fintype.card I * error := by
  have he : (𝔼 x, ∏ i, ∑ j, c i j * A i j x) =
      ∑ choice : I → J, (∏ i, c i (choice i)) * (𝔼 x, ∏ i, A i (choice i) x) := by
    simp only [Fintype.prod_sum, Finset.prod_mul_distrib, Finset.expect_sum_comm, ← Finset.mul_expect]
  rw [he]
  calc
    _ ≤ ∑ choice : I → J, ‖(∏ i, c i (choice i)) * (𝔼 x, ∏ i, A i (choice i) x)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _choice : I → J, error := by
      apply Finset.sum_le_sum
      intro choice _
      simpa only [norm_mul, norm_prod, hc, Finset.prod_const_one, one_mul] using hA choice
    _ = _ := by simp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FiniteKernelCounting
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem subset_counting_error_scale {m n : ℕ} (hmn : m < n) {delta : ℝ} (hdelta : 0 ≤ delta) :
    (18 : ℝ) ^ m * delta ≤ ((18 : ℝ) ^ n * delta) / 18 := by
  calc
    (18 : ℝ) ^ m * delta = ((18 : ℝ) ^ (m + 1) * delta) / 18 := by rw [pow_succ]; ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hdelta)
      (by norm_num)

theorem finite_products_near_one_of_kernel_bound {I X : Type*}
    [DecidableEq I] [Fintype X] [Nonempty X] (s : ℕ) {delta : ℝ} (hdelta : 0 < delta)
    (F : I → X → ℝ) (hmean : ∀ i, |(𝔼 x, F i x) - 1| ≤ delta)
    (hkernel : ∀ (S : Finset I), S.card ≤ s → ∀ i j : I, i ∉ S → j ∉ S → i ≠ j →
      ∀ b : ℝ, (b = 1 ∨ b = 1 / 4) →
        countingKernelAverage b (fun x => ∏ k ∈ S, F k x) (F i) (F j) ≤ 1 + delta / 16)
    (T : Finset I) (hT : T.card ≤ s + 2) :
    |(𝔼 x, ∏ i ∈ T, F i x) - 1| ≤ (18 : ℝ) ^ T.card * delta := by
  induction T using Finset.strongInductionOn
  rename_i T ih
  rcases T.eq_empty_or_nonempty with rfl | hnonempty
  · simp only [Finset.prod_empty, Fintype.expect_const, sub_self, abs_zero,
      Finset.card_empty, pow_zero, one_mul]
    exact le_of_lt hdelta
  by_cases hsmall : T.card ≤ 1
  · obtain ⟨i, hi⟩ := hnonempty
    have heq : T = {i} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hi, fun j hj => Finset.card_le_one.mp hsmall j hj i hi⟩
    rw [heq]
    simp only [Finset.prod_singleton, Finset.card_singleton, pow_one]
    exact (hmean i).trans (by linarith)
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (show 1 < T.card by omega)
  let S := (T.erase i).erase j
  have hj' : j ∈ T.erase i := Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩
  have hSi : i ∉ S := by simp [S]
  have hSj : j ∉ S := by simp [S]
  have hSji : insert j S = T.erase i := Finset.insert_erase hj'
  have hSij : insert i S = T.erase j := by
    dsimp [S]
    rw [Finset.erase_right_comm, Finset.insert_erase (Finset.mem_erase.mpr ⟨hij, hi⟩)]
  have hform : T = insert i (insert j S) := by rw [hSji, Finset.insert_erase hi]
  have hScard : S.card ≤ s := by
    dsimp [S]
    rw [Finset.card_erase_of_mem hj', Finset.card_erase_of_mem hi]
    omega
  have hproper (U : Finset I) (hU : U ⊂ T) :
      |(𝔼 x, ∏ k ∈ U, F k x) - 1| ≤ ((18 : ℝ) ^ T.card * delta) / 18 :=
    (ih U hU ((Finset.card_le_card (le_of_lt hU)).trans hT)).trans
      (subset_counting_error_scale (Finset.card_lt_card hU) (le_of_lt hdelta))
  have h00 := hproper S (lt_of_le_of_lt (Finset.erase_subset j (T.erase i))
    (Finset.erase_ssubset hi))
  have h10 : |(𝔼 x, (∏ k ∈ S, F k x) * F i x) - 1| ≤
      ((18 : ℝ) ^ T.card * delta) / 18 := by
    have h := hproper (insert i S) (by rw [hSij]; exact Finset.erase_ssubset hj)
    simpa only [Finset.prod_insert hSi, mul_comm] using h
  have h01 : |(𝔼 x, (∏ k ∈ S, F k x) * F j x) - 1| ≤
      ((18 : ℝ) ^ T.card * delta) / 18 := by
    have h := hproper (insert j S) (by rw [hSji]; exact Finset.erase_ssubset hi)
    simpa only [Finset.prod_insert hSj, mul_comm] using h
  have hprod (x : X) : (∏ k ∈ T, F k x) = (∏ k ∈ S, F k x) * F i x * F j x := by
    rw [hform, Finset.prod_insert (by simp [hij, hSi]), Finset.prod_insert hSj]
    ring
  by_contra! hbad
  simp only [hprod] at hbad
  obtain ⟨b, hb, hsurplus⟩ := exists_countingKernel_surplus
    (mul_pos (pow_pos (by norm_num) _) hdelta) (fun x => ∏ k ∈ S, F k x)
    (F i) (F j) h00 h10 h01 hbad
  have hu := hkernel S hScard i j hSi hSj hij b hb
  have hscale : delta ≤ (18 : ℝ) ^ T.card * delta := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (one_le_pow₀ (show (1 : ℝ) ≤ 18 by norm_num)) (le_of_lt hdelta)
  linarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProgressionKernelBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_progression_kernel_bound (s : ℕ) {tau : ℝ} (htau : 0 < tau) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi0 : ℝ, 0 < xi0 ∧
    ∀ {N : ℕ} [NeZero N] {p xi : ℝ}, 2 ≤ p → 0 < xi → xi ≤ xi0 →
      Odd N → Real.exp ((p + 2) ^ C) ≤ N →
      ∀ {I : Type} [DecidableEq I] (slopes : I → ZMod N) (mu : I → ZMod N → ℝ)
        (a b : ZMod N) (parameter : ℝ) (f g : ZMod N → ℝ),
      0 ≤ parameter → parameter ≤ 1 →
      (∀ i x, 0 ≤ mu i x ∧ mu i x ≤ Real.exp p) →
      (∀ i, CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) (mu i) (fun _ => 1 + xi)) →
      (∀ x, 0 ≤ f x ∧ f x ≤ Real.exp p) →
      CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) f (fun _ => 1 + xi) →
      (∀ x, 0 ≤ g x ∧ g x ≤ Real.exp p) →
      CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) g (fun _ => 1 + xi) →
      ∀ S : Finset I, S.card ≤ s → IsUnit (b - a) →
        (∀ i ∈ S, IsUnit (a - slopes i) ∧ IsUnit (b - slopes i)) →
        (∀ i ∈ S, ∀ j ∈ S, i ≠ j → IsUnit (slopes i - slopes j)) →
        |𝔼 x, 𝔼 d, (∏ i ∈ S, mu i (x + slopes i * d)) *
          countingKernel parameter (f (x + a * d)) (g (x + b * d))| < 1 + tau := by
  obtain ⟨delta, hdelta, C0, hC0, hparameters⟩ := exists_counting_kernel_parameters s htau
  obtain ⟨C, hC, xi0, hxi0, hstage⟩ := exists_pivot_stage_bound s hdelta hC0
  refine ⟨C, hC, xi0, hxi0, ?_⟩
  intro N _ p xi hp hxi hxib hodd hN I _ slopes mu a b parameter f g
    hparameter hparameter1 hmu hcompare hf hfcompare hg hgcompare S hS hab hends hpairs
  obtain ⟨n, hqcap, hsmall⟩ := hparameters p hp
  let v : Fin 0 → ZMod N := Fin.elim0
  have hc := pivotCompatible_zero v S slopes a b hab hends hpairs
  have h := hstage hp hxi hxib hodd hN n hqcap slopes mu a b parameter f g
    hparameter hparameter1 hmu hcompare hf hfcompare hg hgcompare v S
    (by simpa only [zero_add] using hS) hc
  rw [pivotStageCount_zero] at h
  simpa only [pow_zero] using h.trans_lt (hsmall S.card hS)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MaskedCenteredCounting
namespace OAI

universe u

section

namespace Erdos3

open scoped BigOperators

theorem maskedNormalized_bounds {X : Type*} (mu phi : X → ℝ) {B : ℝ} (hB : 1 ≤ B)
    (hmu : ∀ x, 0 ≤ mu x ∧ mu x ≤ B) (hphi : ∀ x, 0 ≤ phi x ∧ phi x ≤ 1) (x : X) :
    0 ≤ maskedNormalized mu phi x ∧ maskedNormalized mu phi x ≤ B := by
  have h1 := mul_nonneg (hphi x).1 (hmu x).1
  have h2 := mul_nonneg (hphi x).1 (sub_nonneg.mpr (hmu x).2)
  have h3 := mul_nonneg (sub_nonneg.mpr (hphi x).2) (sub_nonneg.mpr hB)
  dsimp [maskedNormalized]
  constructor <;> nlinarith [(hphi x).2]

theorem maskedNormalized_score_le {X : Type*} (mu phi : X → ℝ) {xi xi' : ℝ}
    (hxi : 0 ≤ xi) (hxi' : xi ≤ xi') (hphi : ∀ x, phi x ≤ 1) (x : X) :
    maskedNormalized mu phi x - (1 + xi') ≤ mu x * phi x - (1 + xi) * phi x := by
  have h := mul_le_mul_of_nonneg_left (hphi x) hxi
  dsimp [maskedNormalized]
  nlinarith

theorem maskedNormalized_mean {X : Type*} [Fintype X] [Nonempty X]
    (mu phi : X → ℝ) {xi error : ℝ} (hxi : 0 ≤ xi)
    (hmean : (𝔼 x, mu x) = 1) (hphi : ∀ x, 0 ≤ phi x ∧ phi x ≤ 1)
    (hupper : (𝔼 x, (mu x - (1 + xi)) * phi x) ≤ error)
    (hlower : (𝔼 x, (mu x - (1 + xi)) * (1 - phi x)) ≤ error) :
    |(𝔼 x, maskedNormalized mu phi x) - 1| ≤ xi + error := by
  have hphimean : 0 ≤ (𝔼 x, phi x) ∧ (𝔼 x, phi x) ≤ 1 := by
    constructor
    · exact Finset.expect_nonneg (fun x _ => (hphi x).1)
    · exact (Finset.expect_le_expect (fun x _ => (hphi x).2)).trans_eq (Fintype.expect_const 1)
  have he (x : X) : maskedNormalized mu phi x = 1 + (mu x - (1 + xi)) * phi x + xi * phi x := by
    dsimp [maskedNormalized]
    ring
  have hcomp (x : X) : (mu x - (1 + xi)) * (1 - phi x) =
      mu x - (1 + xi) - (mu x - (1 + xi)) * phi x := by ring
  simp only [hcomp, Finset.expect_sub_distrib, Fintype.expect_const, hmean] at hlower
  simp only [he, Finset.expect_add_distrib, Fintype.expect_const, ← Finset.mul_expect]
  apply abs_le.mpr
  constructor <;> nlinarith [mul_nonneg hxi hphimean.1,
    mul_le_mul_of_nonneg_left hphimean.2 hxi]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem CyclicNiltestUpperComparison.masked {degree N : ℕ} [NeZero N]
    {P R error xi xi' : ℝ} {mu phi : ZMod N → ℝ}
    (hcompare : CyclicNiltestUpperComparison.{u} degree N P error mu (fun _ => 1 + xi))
    (hphi : PositiveCyclicNiltest.{u} degree N R phi) (hR : 0 ≤ R)
    (hbudget : productNiltestBudget (raisedNiltestBudget R) ≤ P)
    (hxi : 0 ≤ xi) (hxi' : xi ≤ xi') :
    CyclicNiltestUpperComparison.{u} degree N R error
      (maskedNormalized mu phi) (fun _ => 1 + xi') := by
  have h : CyclicNiltestUpperComparison.{u} degree N R error
      (fun x => mu x * phi x) (fun x => (1 + xi) * phi x) :=
    hphi.mul_upperComparison (low := degree) (@hcompare) le_rfl hR hbudget
  intro L _ _ s dim _ _ _ _ D hs T hT hTc
  apply le_trans _ (h D hs T hT hTc)
  apply Finset.expect_le_expect
  intro x _
  exact mul_le_mul_of_nonneg_right
    (maskedNormalized_score_le mu phi hxi hxi' (fun y => (hphi.unit_interval y).2) x)
    (T.unit_interval_evalCyclic hT N (fun _ => x)).2.1

theorem CyclicNiltestUpperComparison.masked_mean {degree N : ℕ} [NeZero N]
    {P R error xi : ℝ} {mu phi : ZMod N → ℝ}
    (hcompare : CyclicNiltestUpperComparison.{u} degree N P error mu (fun _ => 1 + xi))
    (hphi : PositiveCyclicNiltest.{u} degree N R phi) (hRP : R + 1 ≤ P)
    (hxi : 0 ≤ xi) (hmean : (𝔼 x, mu x) = 1) :
    |(𝔼 x, maskedNormalized mu phi x) - 1| ≤ xi + error :=
  maskedNormalized_mean mu phi hxi hmean hphi.unit_interval
    (hcompare.test_positive hphi (by linarith))
    (hcompare.test_positive hphi.complement hRP)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_positive_progression_counting (s : ℕ) {tau : ℝ} (htau : 0 < tau) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi0 : ℝ, 0 < xi0 ∧
    ∀ {N : ℕ} [NeZero N] {p xi : ℝ}, 2 ≤ p → 0 < xi → xi ≤ xi0 →
      Odd N → Real.exp ((p + 2) ^ C) ≤ N →
      ∀ {I : Type} [DecidableEq I] (slopes : I → ZMod N) (mu : I → ZMod N → ℝ),
      (∀ i j, i ≠ j → IsUnit (slopes i - slopes j)) →
      (∀ i x, 0 ≤ mu i x ∧ mu i x ≤ Real.exp p) →
      (∀ i, |(𝔼 x, mu i x) - 1| ≤ 2 * xi) →
      (∀ i, CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) (mu i) (fun _ => 1 + xi)) →
      ∀ T : Finset I, T.card ≤ s + 2 →
        |(𝔼 x, 𝔼 d, ∏ i ∈ T, mu i (x + slopes i * d)) - 1| ≤ tau := by
  let delta := tau / (18 : ℝ) ^ (s + 2)
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  obtain ⟨C, hC, xi1, hxi1, hkernel⟩ := exists_progression_kernel_bound s
    (show 0 < delta / 16 by positivity)
  refine ⟨C, hC, min xi1 (delta / 2), lt_min hxi1 (by positivity), ?_⟩
  intro N _ p xi hp hxi hxib hodd hN I _ slopes mu hsep hmu hmean hcompare T hT
  have hxi1b : xi ≤ xi1 := hxib.trans (min_le_left _ _)
  have hxid : 2 * xi ≤ delta := by
    have h := hxib.trans (min_le_right xi1 (delta / 2))
    linarith
  let F : I → (ZMod N × ZMod N) → ℝ := fun i z => mu i (z.1 + slopes i * z.2)
  have hmeanF (i : I) : |(𝔼 z, F i z) - 1| ≤ delta := by
    dsimp only [F]
    rw [expect_prod_split, expect_single_slope]
    exact (hmean i).trans hxid
  have hkernelF (S : Finset I) (hS : S.card ≤ s) (i j : I)
      (hi : i ∉ S) (hj : j ∉ S) (hij : i ≠ j) (b : ℝ) (hb : b = 1 ∨ b = 1 / 4) :
      countingKernelAverage b (fun z => ∏ k ∈ S, F k z) (F i) (F j) ≤ 1 + delta / 16 := by
    have hb0 : 0 ≤ b := by rcases hb with rfl | rfl <;> norm_num
    have hb1 : b ≤ 1 := by rcases hb with rfl | rfl <;> norm_num
    have h := hkernel hp hxi hxi1b hodd hN slopes mu (slopes i) (slopes j) b (mu i) (mu j)
      hb0 hb1 hmu hcompare (hmu i) (@hcompare i) (hmu j) (@hcompare j) S hS
      (hsep j i (Ne.symm hij))
      (fun k hk => ⟨hsep i k (by rintro rfl; exact hi hk),
        hsep j k (by rintro rfl; exact hj hk)⟩)
      (fun k _ l _ hkl => hsep k l hkl)
    unfold countingKernelAverage
    rw [expect_prod_split]
    exact (le_abs_self _).trans (le_of_lt h)
  have h := finite_products_near_one_of_kernel_bound s hdelta F hmeanF hkernelF T hT
  dsimp only [F] at h
  rw [expect_prod_split] at h
  apply h.trans
  calc
    (18 : ℝ) ^ T.card * delta ≤ (18 : ℝ) ^ (s + 2) * delta :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hT) (le_of_lt hdelta)
    _ = tau := by dsimp [delta]; field_simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_masked_positive_counting (s a : ℕ) {tau : ℝ} (htau : 0 < tau) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi : ℝ, 0 < xi ∧
    ∀ {N : ℕ} [NeZero N] {p : ℝ}, 2 ≤ p → Odd N → Real.exp ((p + 2) ^ C) ≤ N →
      ∀ mu : ZMod N → ℝ, (∀ x, 0 ≤ mu x ∧ mu x ≤ Real.exp p) → (𝔼 x, mu x) = 1 →
      CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) mu (fun _ => 1 + xi) →
      ∀ {I : Type} [DecidableEq I] (slopes : I → ZMod N) (phi : I → ZMod N → ℝ),
      (∀ i j, i ≠ j → IsUnit (slopes i - slopes j)) →
      (∀ i, PositiveCyclicNiltest.{0} s N ((p + 2) ^ a) (phi i)) →
      ∀ T : Finset I, T.card ≤ s + 2 →
        |(𝔼 x, 𝔼 d, ∏ i ∈ T, maskedNormalized mu (phi i) (x + slopes i * d)) - 1| ≤ tau := by
  obtain ⟨B, _, xi, hxi, hcount⟩ := exists_positive_progression_counting s htau
  obtain ⟨C, hC, hbudget⟩ := exists_masked_comparison_budget a B hxi
  refine ⟨C, hC, xi, hxi, ?_⟩
  intro N _ p hp hodd hN mu hmu hmean hcompare I _ slopes phi hsep hphi T hT
  obtain ⟨haR, hBR, hRP, hproduct, herror⟩ := hbudget p hp
  let R := (p + 2) ^ (max a B)
  have hR : 0 ≤ R := pow_nonneg (by linarith) _
  have hBP : (p + 2) ^ B ≤ (p + 2) ^ C := by linarith
  have hphiR (i : I) : PositiveCyclicNiltest.{0} s N R (phi i) :=
    (hphi i).mono le_rfl haR
  apply hcount (N := N) (p := p) (xi := xi) hp hxi le_rfl hodd
    ((Real.exp_le_exp.mpr hBP).trans hN) slopes (fun i => maskedNormalized mu (phi i)) hsep
    (fun i x => maskedNormalized_bounds mu (phi i) (Real.one_le_exp (by linarith))
      hmu (hphiR i).unit_interval x) ?_ ?_ T hT
  · intro i
    have h := CyclicNiltestUpperComparison.masked_mean hcompare (hphiR i) hRP hxi.le hmean
    exact h.trans (by linarith)
  · intro i
    exact CyclicNiltestUpperComparison.mono_budget
      (CyclicNiltestUpperComparison.masked hcompare (hphiR i) hR hproduct hxi.le le_rfl)
      hBR (Real.exp_le_exp.mpr (neg_le_neg hBP))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_masked_centered_counting (s a : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi : ℝ, 0 < xi ∧
    ∀ {N : ℕ} [NeZero N] {p : ℝ}, 2 ≤ p → Odd N → Real.exp ((p + 2) ^ C) ≤ N →
      ∀ mu : ZMod N → ℝ, (∀ x, 0 ≤ mu x ∧ mu x ≤ Real.exp p) → (𝔼 x, mu x) = 1 →
      CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) mu (fun _ => 1 + xi) →
      ∀ {I : Type} [DecidableEq I] (slopes : I → ZMod N) (phi : I → ZMod N → ℝ),
      (∀ i j, i ≠ j → IsUnit (slopes i - slopes j)) →
      (∀ i, PositiveCyclicNiltest.{0} s N ((p + 2) ^ a) (phi i)) →
      ∀ T : Finset I, T.Nonempty → T.card ≤ s + 2 →
        |𝔼 x, 𝔼 d, ∏ i ∈ T, phi i (x + slopes i * d) * (mu (x + slopes i * d) - 1)| ≤
          epsilon := by
  let tau := epsilon / (2 : ℝ) ^ (s + 2)
  have htau : 0 < tau := by dsimp [tau]; positivity
  obtain ⟨C, hC, xi, hxi, hcount⟩ := exists_masked_positive_counting s a htau
  refine ⟨C, hC, xi, hxi, ?_⟩
  intro N _ p hp hodd hN mu hmu hmean hcompare I _ slopes phi hsep hphi T hT hcard
  let F : I → (ZMod N × ZMod N) → ℝ :=
    fun i z => maskedNormalized mu (phi i) (z.1 + slopes i * z.2)
  have hsub (U : Finset I) (hU : U ⊆ T) : |(𝔼 z, ∏ i ∈ U, F i z) - 1| ≤ tau := by
    dsimp only [F]
    rw [expect_prod_split]
    exact hcount hp hodd hN mu hmu hmean hcompare slopes phi hsep hphi U
      ((Finset.card_le_card hU).trans hcard)
  have h := centered_product_mean_abs_le T hT F hsub
  have heq (i : I) (z : ZMod N × ZMod N) :
      F i z - 1 = phi i (z.1 + slopes i * z.2) * (mu (z.1 + slopes i * z.2) - 1) := by
    dsimp [F, maskedNormalized]
    ring
  simp only [heq] at h
  rw [expect_prod_split] at h
  apply h.trans
  calc
    (2 : ℝ) ^ T.card * tau ≤ (2 : ℝ) ^ (s + 2) * tau :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hcard) htau.le
    _ = epsilon := by dsimp [tau]; field_simp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CharacterCenteredCounting
namespace OAI

section

namespace Erdos3

open scoped TensorProduct NNReal

theorem positiveCyclicNiltest_characterMask {N degree : ℕ} [NeZero N]
    (hdegree : 1 ≤ degree) (chi : AddChar (ZMod N) ℂ) (t : Bool × Bool) :
    PositiveCyclicNiltest.{0} degree N 13 (fun x => complexPositiveMask t (chi x)) := by
  obtain ⟨T, hTnorm, hTc, hTeval⟩ := exists_cyclic_character_niltest chi
  have hbound (z) := complexPositiveMask_bounds t ((T.norm_le z).trans (by exact_mod_cast hTnorm))
  let S : (RationalTorus.nilmanifold 1).Niltest (fun _ : Unit => 1) := {
    orbit := T.orbit
    observable := fun z => (complexPositiveMask t (T.observable z) : ℂ)
    normBound := 1
    lipBound := T.lipBound
    norm_le := fun z => by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hbound z).1, NNReal.coe_one] using (hbound z).2
    lipschitz := by
      let := (RationalTorus.nilmanifold 1).metricSpace
      simpa only [one_mul, Function.comp_def] using
        Complex.isometry_ofReal.lipschitz.comp ((complexPositiveMask_lipschitz t).comp T.lipschitz) }
  have hS : S.UnitIntervalValued := by
    intro z
    exact ⟨rfl, hbound z⟩
  have hSc : S.ComplexityLE 13 := by
    refine ⟨hTc.1.mono _ (by norm_num), ?_⟩
    change Real.log (2 + 1 + (T.lipBound : ℝ)) ≤ 13
    apply (Real.log_le_iff_le_exp (by positivity)).2
    have h := T.observable_budget hTc
    have he : Real.exp 13 = Real.exp 12 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [he]
    nlinarith [T.normBound.coe_nonneg, Real.add_one_le_exp (1 : ℝ), Real.exp_pos (12 : ℝ)]
  refine .of_test (RationalTorus.nilmanifold 1) hdegree S hS hSc ?_
  intro x
  change complexPositiveMask t (chi x) = complexPositiveMask t (T.evalCyclic N (fun _ => x))
  rw [hTeval]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_character_centered_counting_oai (s : ℕ) (hs : 1 ≤ s)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi : ℝ, 0 < xi ∧
    ∀ {N : ℕ} [NeZero N] {p : ℝ}, 2 ≤ p → Odd N → Real.exp ((p + 2) ^ C) ≤ N →
      ∀ mu : ZMod N → ℝ, (∀ x, 0 ≤ mu x ∧ mu x ≤ Real.exp p) → (𝔼 x, mu x) = 1 →
      CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) mu (fun _ => 1 + xi) →
      ∀ {I : Type} [Fintype I] [DecidableEq I] [Nonempty I], Fintype.card I ≤ s + 2 →
      ∀ (slopes : I → ZMod N) (chi : I → AddChar (ZMod N) ℂ),
      (∀ i j, i ≠ j → IsUnit (slopes i - slopes j)) →
      ‖𝔼 x, 𝔼 d, ∏ i, chi i (x + slopes i * d) * ((mu (x + slopes i * d) - 1 : ℝ) : ℂ)‖ ≤
        epsilon := by
  let delta := epsilon / (4 : ℝ) ^ (s + 2)
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  obtain ⟨C, hC, xi, hxi, hcount⟩ := exists_masked_centered_counting s 2 hdelta
  refine ⟨C, hC, xi, hxi, ?_⟩
  intro N _ p hp hodd hN mu hmu hmean hcompare I _ _ _ hI slopes chi hsep
  let A : I → (Bool × Bool) → (ZMod N × ZMod N) → ℂ := fun i t z =>
    (complexPositiveMask t (chi i (z.1 + slopes i * z.2)) : ℂ) *
      ((mu (z.1 + slopes i * z.2) - 1 : ℝ) : ℂ)
  have hcost : (13 : ℝ) ≤ (p + 2) ^ 2 := by nlinarith
  have hA (choice : I → Bool × Bool) : ‖𝔼 z, ∏ i, A i (choice i) z‖ ≤ delta := by
    let phi : I → ZMod N → ℝ := fun i x => complexPositiveMask (choice i) (chi i x)
    have hphi (i : I) : PositiveCyclicNiltest.{0} s N ((p + 2) ^ 2) (phi i) :=
      (positiveCyclicNiltest_characterMask hs (chi i) (choice i)).mono le_rfl hcost
    have h := hcount hp hodd hN mu hmu hmean hcompare slopes phi hsep hphi
      Finset.univ Finset.univ_nonempty (by simpa using hI)
    have he : (𝔼 z, ∏ i, A i (choice i) z) =
        (((𝔼 x, 𝔼 d, ∏ i, phi i (x + slopes i * d) * (mu (x + slopes i * d) - 1)) : ℝ) : ℂ) := by
      simp only [A, ← Complex.ofReal_mul, ← Complex.ofReal_prod]
      rw [expect_prod_split]
      simp only [phi, Fintype.expect_eq_sum_div_card, Complex.ofReal_div,
        Complex.ofReal_sum, Complex.ofReal_natCast]
    rw [he]
    simpa only [Complex.norm_real, Real.norm_eq_abs] using h
  have h := norm_expect_product_sum_le (fun _ : I => complexMaskCoefficient) A
    (fun _ t => complexMaskCoefficient_norm t) hA
  have he (i : I) (z : ZMod N × ZMod N) :
      (∑ t, complexMaskCoefficient t * A i t z) =
        chi i (z.1 + slopes i * z.2) * ((mu (z.1 + slopes i * z.2) - 1 : ℝ) : ℂ) := by
    dsimp only [A]
    simp only [← mul_assoc]
    rw [← Finset.sum_mul]
    congr 1
    exact (complexPositiveMask_expansion _).symm
  simp only [he, Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat] at h
  rw [expect_prod_split] at h
  apply h.trans
  calc
    ((2 : ℝ) * 2) ^ Fintype.card I * delta ≤ (4 : ℝ) ^ (s + 2) * delta := by
      norm_num only [show (2 : ℝ) * 2 = 4 by norm_num]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hI) hdelta.le
    _ = epsilon := by dsimp [delta]; field_simp

end Erdos3

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.exists_character_centered_counting_oai := @OAI.Erdos3.exists_character_centered_counting_oai

-- Prove2me | solution 1 for GlobalTheory.ThetaInter.mean_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:39.401956+00:00
-- url     : https://prove2.me/submissions/d3a4c9a4-a9f0-4dd0-8d40-6d822604fb98

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaInter
open Formalism.L2.Th1.H Complex
open scoped BigOperators ComplexConjugate
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {H : Sesq V}
variable {α : V → ℂ}
open MeasureTheory
variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedSpace ℝ W] [IsScalarTower ℝ ℂ W]
  [FiniteDimensional ℝ W] {H : Sesq W} {α : W → ℂ}
variable [MeasurableSpace W] [BorelSpace W] (μ : Measure W) [μ.IsAddHaarMeasure]
namespace GlobalTheory.ThetaInter
theorem _root_.solution {κ : Type} [Fintype κ] (b : Module.Basis κ ℝ W) {A : AddSubgroup W}
    (hb : (Submodule.span ℤ (Set.range b)).toAddSubgroup = A) {f : W → ℝ} (hf : ∀ x ∈ A, ∀ z, f (z + x) = f z) :
    mean μ A f = ⨍ z in ZSpan.fundamentalDomain b, f z ∂μ := by
  subst hb
  have h1 := ZSpan.isAddFundamentalDomain' b μ
  have h2 := Classical.epsilon_spec
    (p := fun Fd => IsAddFundamentalDomain (Submodule.span ℤ (Set.range b)).toAddSubgroup Fd μ) ⟨_, h1⟩
  rw [mean, setAverage_eq, setAverage_eq, measureReal_def, measureReal_def, h2.measure_eq h1,
    h2.setIntegral_eq h1]
  intro g x
  change f ((g : W) + x) = f x
  rw [add_comm]
  exact hf g g.2 x
end GlobalTheory.ThetaInter

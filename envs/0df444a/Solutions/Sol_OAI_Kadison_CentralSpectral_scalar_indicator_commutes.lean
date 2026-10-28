-- Prove2me | solution 1 for OAI.Kadison.CentralSpectral.scalar_indicator_commutes
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:31:02.211612+00:00
-- url     : https://prove2.me/submissions/4b47881a-dc54-4973-8eac-32ff1ebf45db

import Mathlib
import Definitions.Def_OAIQ039C054

section
-- module Solutions.OAIQ039_CM.Commutator_CyclicSpectralUnitary
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.CyclicSpectral

variable {Ω H : Type*} [TopologicalSpace Ω] [T2Space Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (μ : Measure Ω)

omit [T2Space Ω] in
lemma scalarMultiplier_ae (f : C(Ω,ℂ)) (v : Lp ℂ 2 μ) :
    scalarMultiplier μ f v=ᵐ[μ] fun x => f x*v x :=
  Decomposable.operator_ae ..

end Kadison.CyclicSpectral

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_AbelianSpectralIndicators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open MeasureTheory Filter

open scoped Topology InnerProductSpace ComplexOrder

namespace Kadison.CentralSpectral

open CyclicSpectral Decomposable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

variable (τ : (CentralCorner.center M) →ₚ[ℂ] ℂ)

variable (μ : Measure (Spectrum M))

variable (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] τ.GNS)

lemma scalar_indicator_commutes_oai (f : C(Spectrum M,ℂ)) (s : Set (Spectrum M)) (hs : MeasurableSet s) :
    Commute (scalarMultiplier μ f) (indicatorOperator (H:=ℂ) μ s hs) := by
  classical
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  filter_upwards [scalarMultiplier_ae μ f (indicatorOperator μ s hs v),
    indicatorOperator_ae μ s hs v,indicatorOperator_ae μ s hs (scalarMultiplier μ f v),
    scalarMultiplier_ae μ f v] with x h₁ h₂ h₃ h₄
  change scalarMultiplier μ f (indicatorOperator μ s hs v) x=
    indicatorOperator μ s hs (scalarMultiplier μ f v) x
  rw [h₁,h₃]
  by_cases hx : x∈s
  · simp only [Set.indicator_of_mem hx]
    rw [h₂,Set.indicator_of_mem hx,h₄]
  · simp [hx,h₂]

end Kadison.CentralSpectral

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.CentralSpectral.scalar_indicator_commutes_oai.{u_1} := @OAI.Kadison.CentralSpectral.scalar_indicator_commutes_oai.{u_1}

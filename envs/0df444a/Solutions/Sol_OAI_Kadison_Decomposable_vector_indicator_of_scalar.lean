-- Prove2me | solution 1 for OAI.Kadison.Decomposable.vector_indicator_of_scalar
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:38:36.961128+00:00
-- url     : https://prove2.me/submissions/a996d170-8559-4fff-875f-d1c40f4221c4

import Mathlib
import Definitions.Def_OAIQ039C033
import Definitions.Def_OAIQ039C035

section
-- module Solutions.OAIQ039_CM.Commutator_L2InfiniteSumCoordinates
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

open scoped InnerProductSpace Topology ENNReal

namespace Kadison.Decomposable

open InfiniteAmplification

local instance l2InfiniteSumCoordinatesDecidableEq_r4a7783_1 {α : Sort*} : DecidableEq α := Classical.decEq α
variable {Ω H ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [Countable ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [TopologicalSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

lemma scalarVectorMultiplier_ae (f : C(Ω,ℂ)) (v : Lp H 2 μ) :
    scalarVectorMultiplier μ f v=ᵐ[μ] fun x => f x • v x := operator_ae ..

omit [Countable ι] in
lemma evalL_scalarMultiplier (i : ι) (f : C(Ω,ℂ)) (v : Lp (Space ι H) 2 μ) :
    evalL μ i (scalarVectorMultiplier μ f v)=scalarVectorMultiplier μ f (evalL μ i v) := by
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLp (lp.evalCLM ℂ (fun _ : ι => H) 2 i)
    (scalarVectorMultiplier μ f v),scalarVectorMultiplier_ae μ f v,
    scalarVectorMultiplier_ae μ f (evalL μ i v),
    ContinuousLinearMap.coeFn_compLp (lp.evalCLM ℂ (fun _ : ι => H) 2 i) v] with x h₁ h₂ h₃ h₄
  change ((lp.evalCLM ℂ (fun _ : ι => H) 2 i).compLp (scalarVectorMultiplier μ f v)) x=_
  rw [h₁,h₃]
  change (scalarVectorMultiplier μ f v) x i=f x • ((lp.evalCLM ℂ (fun _ : ι => H) 2 i).compLp v) x
  rw [h₂,h₄]
  rfl

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_StableScalarGeometry
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

namespace Kadison.Decomposable

open InfiniteAmplification

variable {Ω H ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [Countable ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [Countable ι] [CompleteSpace H] in
lemma evalL_indicator (i : ι) (s : Set Ω) (hs : MeasurableSet s) (v : Lp (Space ι H) 2 μ) :
    evalL μ i (indicatorOperator μ s hs v)=indicatorOperator μ s hs (evalL μ i v) := by
  classical
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLp (lp.evalCLM ℂ (fun _ : ι => H) 2 i)
    (indicatorOperator μ s hs v),indicatorOperator_ae μ s hs v,
    indicatorOperator_ae μ s hs (evalL μ i v),
    ContinuousLinearMap.coeFn_compLp (lp.evalCLM ℂ (fun _ : ι => H) 2 i) v] with x h₁ h₂ h₃ h₄
  change ((lp.evalCLM ℂ (fun _ : ι => H) 2 i).compLp (indicatorOperator μ s hs v)) x=_
  rw [h₁,h₃]
  change (indicatorOperator μ s hs v) x i=s.indicator (evalL μ i v) x
  rw [h₂]
  by_cases hx : x∈s
  · simp only [Set.indicator_of_mem hx]
    exact h₄.symm
  · simp [hx]

variable [TopologicalSpace Ω] [T2Space Ω] [CompactSpace Ω] [BorelSpace Ω]

omit [T2Space Ω] in
lemma vector_indicator_of_scalar_oai (f : C(Ω,ℂ)) (s : Set Ω) (hs : MeasurableSet s)
    (hf : CyclicSpectral.scalarMultiplier μ f=indicatorOperator μ s hs) :
    scalarVectorMultiplier (H:=Space ι ℂ) μ f=indicatorOperator μ s hs := by
  apply ContinuousLinearMap.ext
  intro v
  apply sub_eq_zero.mp
  apply evalL_separates μ
  intro i
  rw [map_sub,evalL_scalarMultiplier,evalL_indicator]
  change (CyclicSpectral.scalarMultiplier μ f) (evalL μ i v)-indicatorOperator μ s hs (evalL μ i v)=0
  rw [hf,sub_self]

end Kadison.Decomposable

end

end
end

end OAI
end

theorem solution.{u_1, u_3} : type_of% @OAI.Kadison.Decomposable.vector_indicator_of_scalar_oai.{u_1, u_3} := @OAI.Kadison.Decomposable.vector_indicator_of_scalar_oai.{u_1, u_3}

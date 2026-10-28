-- Prove2me | solution 1 for OAI.Kadison.OrbitStateHull.hull_norm_separable
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:39:39.819588+00:00
-- url     : https://prove2.me/submissions/99a3d1df-2585-47d1-a8d3-684935017c6c

import Mathlib
import Definitions.Def_OAIQ039C040
import Definitions.Def_OAIQ039C056
import Theorems.Thm_OAI_Kadison_OrbitStateHull_hull_projectionContinuousAtOne
import Theorems.Thm_OAI_Kadison_PositiveWOT_mem_predual

section
-- module Solutions.OAIQ039_CM.Commutator_NormalPredual
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter ContinuousLinearMapWOT

open scoped Topology InnerProductSpace

namespace Kadison.NormalPredual

open FiniteStrongTest

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma finiteTests_separable [TopologicalSpace.SeparableSpace H]
    (M : VonNeumannAlgebra H) (v : ℕ → H) : TopologicalSpace.IsSeparable (finiteTests M v) := by
  apply TopologicalSpace.IsSeparable.iUnion
  intro N
  apply TopologicalSpace.isSeparable_range
  exact (innerSL ℂ).continuous.clm_comp_const (testMap M v N)

end Kadison.NormalPredual

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteFactorTrace
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.OrbitStateHull

open PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [Nontrivial H] [TopologicalSpace.SeparableSpace H]

variable (M : VonNeumannAlgebra H) (hfac : FactorCorner.IsFactor M)
  (hd : DiffuseProjection.HasNoMinimalProjections M) (hfin : IsFiniteAlgebra M)

include hfac hd hfin

theorem hull_norm_separable_oai (x : H) :
    TopologicalSpace.IsSeparable (WeakDual.toStrongDual '' hull M x) := by
  apply (NormalPredual.finiteTests_separable M (TopologicalSpace.denseSeq H)).closure.mono
  rintro _ ⟨f,hf,rfl⟩
  exact PositiveWOT.mem_predual M (positive M x f hf)
    (hull_projectionContinuousAtOne M hfac hd hfin x hf)

end Kadison.OrbitStateHull

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.OrbitStateHull.hull_norm_separable_oai.{u_1} := @OAI.Kadison.OrbitStateHull.hull_norm_separable_oai.{u_1}

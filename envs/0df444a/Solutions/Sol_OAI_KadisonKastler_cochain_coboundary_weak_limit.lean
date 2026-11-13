-- Prove2me | solution 1 for OAI.KadisonKastler.cochain_coboundary_weak_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:52:08.103203+00:00
-- url     : https://prove2.me/submissions/d956c22b-327d-4af5-9527-a0c30128f87d

import Mathlib
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_Q260K002
import Definitions.Def_Q260K005

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AsymptoticRowCochain
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.Tracial.conjugateLinear_one _root_.OAI.Generator.Tracial.quotientInclusion_mk _root_.OAI.Generator.Tracial.quotientInclusion_trace _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.NaimarkZFC.gns_apply_coe _root_.OAI.UltrapowerBridge.quotientMap_smul _root_.OAI.UltrapowerBridge.quotientMap_star _root_.OAI.UltrapowerBridge.quotientTrace_mk _root_.OAI.UltrapowerBridge.quotientTrace_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Passage from asymptotically modular row averages to a quadratic cochain.
The asymptotic modularity hypothesis is explicit; its general construction is
not asserted by this adapter. -/

namespace KadisonKastler

noncomputable section

open Filter
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance asymptoticRowAlgebraOrder_r7332ba_1 (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance asymptoticRowAlgebraStarOrder_r7332ba_1 (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
theorem cochain_coboundary_weak_limit_oai (M : VonNeumannAlgebra H)
    {ι : Type*} (ω : Ultrafilter ι) (F : ι → Algebra M →ₗ[ℂ] Algebra M)
    (L : Algebra M →ₗ[ℂ] Algebra M)
    (ht : ∀ a ξ η, Tendsto (fun i => inner ℂ η ((F i a : H →L[ℂ] H) ξ))
      (ω : Filter ι) (𝓝 (inner ℂ η ((L a : H →L[ℂ] H) ξ)))) :
    ∀ a b ξ η, Tendsto (fun i => inner ℂ η ((linearCoboundary (F i) a b : H →L[ℂ] H) ξ))
      (ω : Filter ι) (𝓝 (inner ℂ η ((linearCoboundary L a b : H →L[ℂ] H) ξ))) := by
  intro a b ξ η
  have h := ((ht b ξ ((a : H →L[ℂ] H).adjoint η)).sub (ht (a * b) ξ η)).add
    (ht a ((b : H →L[ℂ] H) ξ) η)
  simpa [linearCoboundary_apply, inner_sub_right, inner_add_right,
    mul_apply_eq_comp, ContinuousLinearMap.adjoint_inner_left] using h

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.cochain_coboundary_weak_limit_oai.{u_1, u_2} := @OAI.KadisonKastler.cochain_coboundary_weak_limit_oai.{u_1, u_2}

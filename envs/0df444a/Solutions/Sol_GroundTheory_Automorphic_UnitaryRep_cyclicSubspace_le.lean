-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.cyclicSubspace_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:45:20.950427+00:00
-- url     : https://prove2.me/submissions/942a198b-f3c9-410b-b0cc-f7d737b72919

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations
import Definitions.Def_GroundTheory_AutomorphicForms_DiscreteSpectrumAbstract

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.UnitaryRep
open MeasureTheory Filter Topology Module End
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap
noncomputable section
variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (π : UnitaryRep G H) (μ : Measure G)
variable {π μ}
omit [MeasurableSpace G] [OpensMeasurableSpace G]
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution {v : H} {V : Submodule ℂ H} (hcl : IsClosed (V : Set H))
    (hV : π.IsInvariant V) (hv : v ∈ V) : π.cyclicSubspace v ≤ V :=
  Submodule.topologicalClosure_minimal _
    (Submodule.span_le.2 (by rintro _ ⟨g, rfl⟩; exact hV g v hv)) hcl
end GroundTheory.Automorphic.UnitaryRep

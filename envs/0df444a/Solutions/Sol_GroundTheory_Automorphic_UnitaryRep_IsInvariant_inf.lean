-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.IsInvariant.inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:45:15.453399+00:00
-- url     : https://prove2.me/submissions/7b18d074-e714-4346-89ce-d08243fe184f

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
namespace IsInvariant
theorem _root_.solution {U V : Submodule ℂ H} (hU : π.IsInvariant U) (hV : π.IsInvariant V) :
    π.IsInvariant (U ⊓ V) :=
  fun g v hv => ⟨hU g v hv.1, hV g v hv.2⟩
end IsInvariant
end GroundTheory.Automorphic.UnitaryRep

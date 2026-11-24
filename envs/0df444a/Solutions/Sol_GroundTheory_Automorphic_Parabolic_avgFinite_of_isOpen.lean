-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.avgFinite_of_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:45:35.358869+00:00
-- url     : https://prove2.me/submissions/f33015e4-c91c-4098-8a9b-2e5d39d01c05

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_relIndex_ne_zero_of_isCompact_of_isOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Set
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {W : Type*} [AddCommGroup W] [Module ℂ W]
omit [AddCommGroup W] [Module ℂ W]
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {K U : Subgroup G} {f : G → W} (hK : IsCompact (K : Set G))
    (hU : IsOpen (U : Set G)) (hUf : U ≤ rightStab f) : AvgFinite K f :=
  relIndex_ne_zero_of_isCompact_of_isOpen hK (Subgroup.isOpen_mono hUf hU)
end GroundTheory.Automorphic.Parabolic

-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.isAdmissible_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:22:27.90518+00:00
-- url     : https://prove2.me/submissions/c0870258-edbb-4734-a959-66b3b03d1c32

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Theorems.Thm_GroundTheory_Automorphic_fixedMap_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal Topology Filter Set MeasureTheory Measure
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  {V' : Type*} [AddCommGroup V'] [Module ℂ V'] {ρ' : Representation ℂ G V'}
omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (hρ : IsSmooth ρ) (hρ' : IsAdmissible ρ')
    (f : Representation.IntertwiningMap ρ ρ') (hf : Function.Injective f) : IsAdmissible ρ := by
  refine ⟨hρ, fun K hKc hKo => ?_⟩
  have := hρ'.2 K hKc hKo
  exact Module.Finite.of_injective (fixedMap ρ f K) (fixedMap_injective ρ hf)
end GroundTheory.Automorphic.Parabolic

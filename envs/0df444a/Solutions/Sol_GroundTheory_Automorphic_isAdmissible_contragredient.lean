-- Prove2me | solution 1 for GroundTheory.Automorphic.isAdmissible_contragredient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:15:29.883042+00:00
-- url     : https://prove2.me/submissions/e3a06644-1f03-4962-9042-59361156a2cd

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Theorems.Thm_GroundTheory_Automorphic_isSmooth_contragredient

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
open Set Filter Topology
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
namespace GroundTheory.Automorphic
theorem _root_.solution (h : IsAdmissible ρ) : IsAdmissible (contragredient ρ) := by
  refine ⟨isSmooth_contragredient ρ, fun K hKc hKo => ?_⟩
  have := h.2 K hKc hKo
  exact LinearEquiv.finiteDimensional (fixedContragredientEquiv h.1 hKc hKo).symm
end GroundTheory.Automorphic

-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.isSmooth_toRepresentation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:40:03.607122+00:00
-- url     : https://prove2.me/submissions/6293ac53-5f40-4a4e-ad0b-57ba93a9c9ae

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingProjective
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingIsotypic

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
open Function Topology
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {V U : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
  {π : Representation ℂ (GL (Fin n) F) V} {ρ : Representation ℂ (GL (Fin n) F) U}
  {ω : GL (Fin n) F → ℂ}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (hρ : IsSmooth ρ) (Y : Subrepresentation ρ) :
    IsSmooth Y.toRepresentation := by
  intro y
  refine Subgroup.isOpen_mono (fun g hg => ?_) (hρ (y : U))
  rw [mem_stabilizerOf] at hg ⊢
  exact Subtype.ext hg
end GroundTheory.Automorphic.Parabolic

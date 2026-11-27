-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.isotypicKernel_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:54:34.32513+00:00
-- url     : https://prove2.me/submissions/cfc1c85f-adc2-4fc2-ae89-429abf707146

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingProjective
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingIsotypic
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_isotypicKernel

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
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (g : GL (Fin n) F) {u : U} (hu : u ∈ isotypicKernel π ρ) :
    ρ g u ∈ isotypicKernel π ρ := by
  rw [mem_isotypicKernel] at hu ⊢
  intro Fm
  rw [Representation.IntertwiningMap.isIntertwining, hu, map_zero]
end GroundTheory.Automorphic.Parabolic

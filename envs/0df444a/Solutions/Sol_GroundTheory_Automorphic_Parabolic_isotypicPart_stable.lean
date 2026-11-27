-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.isotypicPart_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:45:00.235181+00:00
-- url     : https://prove2.me/submissions/f19c3489-48ba-4d24-a0a6-ea36bb99b8d2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingProjective
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingIsotypic
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_apply_mem_isotypicPart

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
theorem _root_.solution (g : GL (Fin n) F) {u : U} (hu : u ∈ isotypicPart π ρ) :
    ρ g u ∈ isotypicPart π ρ := by
  have hle : isotypicPart π ρ ≤ (isotypicPart π ρ).comap (ρ g) := by
    refine iSup_le fun t => ?_
    rintro _ ⟨x, rfl⟩
    rw [Submodule.mem_comap, Representation.IntertwiningMap.toLinearMap_apply,
      ← Representation.IntertwiningMap.isIntertwining]
    exact apply_mem_isotypicPart t (π g x)
  exact hle hu
end GroundTheory.Automorphic.Parabolic

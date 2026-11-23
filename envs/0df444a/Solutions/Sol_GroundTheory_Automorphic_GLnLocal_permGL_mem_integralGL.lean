-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.permGL_mem_integralGL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:05.486889+00:00
-- url     : https://prove2.me/submissions/81b6cade-5bc3-46d7-8a4d-a2e08a79269e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Theorems.Thm_GroundTheory_Automorphic_permGL_apply


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
open Matrix DoubleCoset ValuativeRel
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)
local notation "ϖ" => ((uniformizer F : 𝒪[F]) : F)
omit [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Automorphic.GLnLocal
theorem _root_.solution (σ : Equiv.Perm (Fin n)) : permGL F σ ∈ integralGL F n := by
  rw [mem_integralGL_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [permGL_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  · rw [← map_inv, permGL_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
end GroundTheory.Automorphic.GLnLocal

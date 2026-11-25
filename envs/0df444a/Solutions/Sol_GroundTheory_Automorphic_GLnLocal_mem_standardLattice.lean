-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.mem_standardLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:49:47.8998+00:00
-- url     : https://prove2.me/submissions/db98b10b-ae41-40be-a710-eeda9742e9fb

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice

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
open ValuativeRel Topology Filter Set
open scoped Pointwise Matrix
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] (n : ℕ)
namespace GroundTheory.Automorphic.GLnLocal
theorem _root_.solution {v : Fin n → F} : v ∈ standardLattice F n ↔ ∀ i, v i ∈ 𝒪[F] :=
  Iff.rfl
end GroundTheory.Automorphic.GLnLocal

-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.mem_integralMatrices
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:19.722574+00:00
-- url     : https://prove2.me/submissions/6558b68e-1b08-4ef8-b46b-0a7199c71b78

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal

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
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] (n : ℕ)
namespace GroundTheory.Automorphic.GLnLocal
theorem _root_.solution {A : Matrix (Fin n) (Fin n) F} :
    A ∈ integralMatrices F n ↔ ∀ i j, A i j ∈ 𝒪[F] := by
  constructor
  · rintro ⟨B, rfl⟩ i j
    exact (B i j).2
  · intro h
    exact ⟨Matrix.of fun i j => ⟨A i j, h i j⟩, rfl⟩
end GroundTheory.Automorphic.GLnLocal

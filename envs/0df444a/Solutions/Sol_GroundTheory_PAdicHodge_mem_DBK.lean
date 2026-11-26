-- Prove2me | solution 1 for GroundTheory.PAdicHodge.mem_DBK
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:37:30.140592+00:00
-- url     : https://prove2.me/submissions/b8885e6c-827f-4ce2-9f0f-8b9bfbc01b19

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_Admissible
import Definitions.Def_GroundTheory_PAdicHodge_AdmissibleField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open TensorProduct Module
variable (G F K B : Type*) [Group G] [Field F] [Field K] [CommRing B] [Algebra F K] [Algebra K B]
  [Algebra F B] [IsScalarTower F K B] [MulSemiringAction G B] [SMulCommClass G F B]
  [SMulCommClass G K B]
variable {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V)
variable {G F K B ρ}
theorem _root_.solution {x : B ⊗[F] V} : x ∈ DBK G F K B ρ ↔ ∀ g : G, baseChangeRep B ρ g x = x := by
  first
    | (rfl)
    | (unfold GroundTheory.PAdicHodge.DBK
       simp [Representation.mem_invariants])
    | (exact Representation.mem_invariants _ _)


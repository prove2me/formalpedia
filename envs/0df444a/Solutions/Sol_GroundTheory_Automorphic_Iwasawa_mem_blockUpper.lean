-- Prove2me | solution 1 for GroundTheory.Automorphic.Iwasawa.mem_blockUpper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:04.151944+00:00
-- url     : https://prove2.me/submissions/6915790c-fc4d-4d78-8185-eaed4fba0f7c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa

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
open ValuativeRel Matrix Filter
open scoped Pointwise
open GroundTheory.Automorphic.Iwasawa
open GLnLocal
variable (F : Type*) [Field F] (n : ℕ)
namespace GroundTheory.Automorphic.Iwasawa
theorem _root_.solution {α : Type*} [LinearOrder α] {β : Fin n → α} {g : GL (Fin n) F} :
    g ∈ blockUpper F n β ↔ (g : Matrix (Fin n) (Fin n) F).BlockTriangular β :=
  Iff.rfl
end GroundTheory.Automorphic.Iwasawa

-- Prove2me | solution 1 for GroundTheory.Automorphic.Iwasawa.mem_unipotent
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:36.691751+00:00
-- url     : https://prove2.me/submissions/9d4d7d4b-6564-46b4-981c-daf9169d3c0b

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
theorem _root_.solution {g : GL (Fin n) F} :
    g ∈ unipotent F n ↔ (g : Matrix (Fin n) (Fin n) F).IsUpperTriangular ∧ ∀ i, g i i = 1 :=
  Iff.rfl
end GroundTheory.Automorphic.Iwasawa

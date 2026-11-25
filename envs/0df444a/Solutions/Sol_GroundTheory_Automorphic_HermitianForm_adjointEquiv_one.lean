-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.adjointEquiv_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:16:21.965853+00:00
-- url     : https://prove2.me/submissions/762c33b7-a0c7-4a91-bcd7-f0bb0abc661c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjCyclic
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjTorus
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_eq_adjointEquiv_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V : Type*} [AddCommGroup V] [Module E V]
open GroundTheory.Automorphic.HermitianForm
variable (h : HermitianForm F E V)
namespace GroundTheory.Automorphic.HermitianForm
theorem _root_.solution : h.adjointEquiv 1 = 1 := by
  symm
  rw [eq_adjointEquiv_iff]
  intro y x
  rfl
end GroundTheory.Automorphic.HermitianForm

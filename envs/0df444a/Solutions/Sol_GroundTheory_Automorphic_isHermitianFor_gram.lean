-- Prove2me | solution 1 for GroundTheory.Automorphic.isHermitianFor_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:03:00.096798+00:00
-- url     : https://prove2.me/submissions/98ff6f1b-1a87-4ea2-8be0-8882b0c20e08

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_QuadraticConj
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Module Matrix
variable (F E : Type*) [Field F] [CommRing E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable (V : Type*) [AddCommGroup V] [Module E V]
variable {F E V}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Automorphic
theorem _root_.solution (h : HermitianForm F E V) (v : Basis ι E V) :
    IsHermitianFor (conjHom F E) (gram h.toSesq v) := by
  ext i j
  simp only [transpose_apply, map_apply, gram_apply]
  exact h.isSymm.eq (v j) (v i)
end GroundTheory.Automorphic

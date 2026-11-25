-- Prove2me | solution 1 for GroundTheory.Automorphic.hermTrace_self_of_hermValue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:12:48.751989+00:00
-- url     : https://prove2.me/submissions/719379b3-b22a-4597-91a4-fd5c081b10e8

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Anisotropic
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_HermTraceSelfOfHermValue
import Theorems.Thm_GroundTheory_Automorphic_baseTrace_algebraMap
import Theorems.Thm_GroundTheory_Automorphic_hermPair_self

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
open Module Matrix TensorProduct
variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι E)
variable (K) (R : Type*) [CommRing R] [Algebra K R]
variable {K H R}
namespace GroundTheory.Automorphic
theorem _root_.solution {x : ι → R ⊗[K] E} {t : R}
    (ht : hermValue K H R x = algebraMap R (R ⊗[K] E) t) : hermTrace K H R x x = 2 * t := by
  rw [hermTrace, hermPair_self, ht, baseTrace_algebraMap]
end GroundTheory.Automorphic

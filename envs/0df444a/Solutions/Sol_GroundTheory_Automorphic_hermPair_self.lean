-- Prove2me | solution 1 for GroundTheory.Automorphic.hermPair_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:02:58.349099+00:00
-- url     : https://prove2.me/submissions/aef6df2b-33ab-4ccb-a5d5-c872f8809fd3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Anisotropic
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_HermTraceSelfOfHermValue

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
theorem _root_.solution (x : ι → R ⊗[K] E) : hermPair K H R x x = hermValue K H R x := rfl
end GroundTheory.Automorphic

-- Prove2me | solution 1 for GroundTheory.Automorphic.hermTrace_tensorMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:10:47.626235+00:00
-- url     : https://prove2.me/submissions/e68f7fe9-99db-4d5d-a507-eb6c9d3724e7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Anisotropic
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_HermTraceSelfOfHermValue
import Theorems.Thm_GroundTheory_Automorphic_baseTrace_tensorMap
import Theorems.Thm_GroundTheory_Automorphic_tensorMap_hermPair

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
theorem _root_.solution {S : Type*} [CommRing S] [Algebra K S] (f : R →ₐ[K] S)
    (x y : ι → R ⊗[K] E) :
    f (hermTrace K H R x y) =
      hermTrace K H S (fun i => tensorMap E f (x i)) (fun i => tensorMap E f (y i)) := by
  rw [hermTrace, hermTrace, ← tensorMap_hermPair, baseTrace_tensorMap]
end GroundTheory.Automorphic

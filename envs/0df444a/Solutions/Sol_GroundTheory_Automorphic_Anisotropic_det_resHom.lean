-- Prove2me | solution 1 for GroundTheory.Automorphic.Anisotropic.det_resHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:17:19.558808+00:00
-- url     : https://prove2.me/submissions/9252d5ed-a366-4b70-9201-57f5b46c6c5d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AnisotropicRestrict
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups
import Definitions.Def_GroundTheory_AutomorphicForms_AnisotropicUnitaryRes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Module Matrix TensorProduct
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Anisotropic
variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Basis κ K E)
variable (R : Type*) [CommRing R] [Algebra K R] {R' : Type*} [CommRing R'] [Algebra K R']
local notation "𝒩" => Fintype.card (ι × κ)
variable {R}
variable (R)
variable {R}
variable (R)
namespace GroundTheory.Automorphic.Anisotropic
theorem _root_.solution (M : Matrix ι ι (R ⊗[K] E)) :
    (resHom b R M).det = (rmat b R M.det).det := by
  show (Matrix.reindex (Fintype.equivFin (ι × κ)) (Fintype.equivFin (ι × κ)) (blockHom b R M)).det = _
  rw [Matrix.det_reindex_self]
  exact (Matrix.det_det M (rmatHom b R).toRingHom).symm
end GroundTheory.Automorphic.Anisotropic

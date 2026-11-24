-- Prove2me | solution 1 for GlobalTheory.LatHecke.glMap_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:37:32.663798+00:00
-- url     : https://prove2.me/submissions/5236baad-8d05-4f65-88b6-518577e461db

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_FiniteResidueFieldPadicInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LatHecke
open scoped TensorProduct
variable (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
variable [IsFractionRing O K] (r : ℕ)
variable {O K r}
omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K]
namespace GlobalTheory.LatHecke
theorem _root_.solution (g : GL (Fin r) K) (I : Ideal O) (L : Submodule O (Fin r → K)) :
    glMap g (I • L) = I • glMap g L := Submodule.map_smul'' _ _ _
end GlobalTheory.LatHecke

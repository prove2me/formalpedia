-- Prove2me | solution 1 for GlobalTheory.LatHecke.relIndex_glMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:37:34.217089+00:00
-- url     : https://prove2.me/submissions/394c9402-0e5e-4bf9-ac86-f037dc702e3f

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
theorem _root_.solution (g : GL (Fin r) K) (M L : Submodule O (Fin r → K)) :
    (glMap g M).toAddSubgroup.relIndex (glMap g L).toAddSubgroup =
      M.toAddSubgroup.relIndex L.toAddSubgroup := by
  have hinj : Function.Injective (Matrix.toLin' (g : Matrix (Fin r) (Fin r) K)) := by
    intro x y h
    have := congrArg (Matrix.toLin' ((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)) h
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec] using this
  exact AddSubgroup.relIndex_map_map_of_injective (f :=
    (Matrix.toLin' (g : Matrix (Fin r) (Fin r) K)).toAddMonoidHom) M.toAddSubgroup L.toAddSubgroup hinj
end GlobalTheory.LatHecke

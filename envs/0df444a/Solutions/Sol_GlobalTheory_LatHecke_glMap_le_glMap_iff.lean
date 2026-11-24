-- Prove2me | solution 1 for GlobalTheory.LatHecke.glMap_le_glMap_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:34.184722+00:00
-- url     : https://prove2.me/submissions/75cc41b4-74b1-4186-9bb8-4efe9113be39

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
    glMap g M ≤ glMap g L ↔ M ≤ L := by
  refine ⟨fun h => ?_, fun h => Submodule.map_mono h⟩
  have h' : glMap g⁻¹ (glMap g M) ≤ glMap g⁻¹ (glMap g L) := Submodule.map_mono h
  rwa [← glMap_mul, ← glMap_mul, inv_mul_cancel, glMap_one, glMap_one] at h'
end GlobalTheory.LatHecke

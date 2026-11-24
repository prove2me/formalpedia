-- Prove2me | solution 1 for GlobalTheory.LatHecke.smul_def
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:34.917649+00:00
-- url     : https://prove2.me/submissions/0b52a5db-2b7a-4768-8d10-7b52b3a833f9

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
namespace GlobalTheory.LatHecke
theorem _root_.solution (g : GL (Fin r) K) (L : Lat O K r) : g • L = glLat g L := rfl
end GlobalTheory.LatHecke

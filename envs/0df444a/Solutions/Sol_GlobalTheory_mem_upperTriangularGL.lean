-- Prove2me | solution 1 for GlobalTheory.mem_upperTriangularGL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:09.690751+00:00
-- url     : https://prove2.me/submissions/39d80eff-8786-4c28-abeb-3d60996b6365

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsAdaptedOfIsLocalRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TensorProduct
open GlobalTheory
noncomputable section
variable (ι R : Type*) [CommRing R] [Fintype ι] [LinearOrder ι]
variable {ι R}
namespace GlobalTheory
theorem _root_.solution {g : GL ι R} :
    g ∈ upperTriangularGL ι R ↔ ∀ i j, j < i → (g : Matrix ι ι R) i j = 0 :=
  ⟨fun h _ _ hij => h hij, fun h _ _ hij => h _ _ hij⟩
end GlobalTheory

-- Prove2me | solution 1 for GlobalTheory.AdLat.UnitRoot.sg_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:21.601941+00:00
-- url     : https://prove2.me/submissions/93edd201-e1e9-4af6-859a-d7cd34dc6603

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIntegralUnitRootNormOneAdele

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.UnitRoot
variable (F : Type) [Field F] [NumberField F]
variable (E : Type) [Field E] [NumberField E] [Algebra F E]
variable {F E}
namespace GlobalTheory.AdLat.UnitRoot
theorem _root_.solution (c : E ≃ₐ[F] E) (a : FiniteAdeleRing (𝓞 F) F) (x : E) :
    sg (FiniteAdeleRing (𝓞 F) F) c (a ⊗ₜ[F] x) = a ⊗ₜ[F] c x := rfl
end GlobalTheory.AdLat.UnitRoot

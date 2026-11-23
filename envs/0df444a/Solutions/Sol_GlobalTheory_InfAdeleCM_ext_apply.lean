-- Prove2me | solution 1 for GlobalTheory.InfAdeleCM.ext_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:34.334079+00:00
-- url     : https://prove2.me/submissions/2abdf77c-7fb9-4efd-8bb1-f0cc5c3102af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
open GlobalTheory GlobalTheory.InfAdeleCM
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.InfAdeleCM
theorem _root_.solution (σ : F →+* ℂ) (a : InfiniteAdeleRing F) :
    ext σ a = InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk σ) (a (InfinitePlace.mk σ)) := rfl
end GlobalTheory.InfAdeleCM

-- Prove2me | solution 1 for GlobalTheory.InfAdeleCM.continuous_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:34.181537+00:00
-- url     : https://prove2.me/submissions/2fb32ccd-0692-48cc-9b5b-84c9780ba5e0

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
theorem _root_.solution (σ : F →+* ℂ) : Continuous (ext σ) :=
  (InfinitePlace.Completion.isometry_extensionEmbedding (InfinitePlace.mk σ)).continuous.comp
    (continuous_apply (InfinitePlace.mk σ))
end GlobalTheory.InfAdeleCM

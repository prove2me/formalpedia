-- Prove2me | solution 1 for GlobalTheory.InfAdeleCM.ext_eq_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:43:50.178204+00:00
-- url     : https://prove2.me/submissions/a58679b5-d44d-4dfc-8fc3-0604e232fd9e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective
import Theorems.Thm_GlobalTheory_InfAdeleCM_ext_apply

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
theorem _root_.solution [IsTotallyReal F] (σ : F →+* ℂ) (a : InfiniteAdeleRing F) :
    ext σ a = (InfinitePlace.Completion.extensionEmbeddingOfIsReal
      (IsTotallyReal.isReal (InfinitePlace.mk σ)) (a (InfinitePlace.mk σ)) : ℝ) := by
  rw [ext_apply, InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
end GlobalTheory.InfAdeleCM

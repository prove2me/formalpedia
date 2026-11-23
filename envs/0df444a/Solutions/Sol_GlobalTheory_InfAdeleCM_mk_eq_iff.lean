-- Prove2me | solution 1 for GlobalTheory.InfAdeleCM.mk_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:06.689102+00:00
-- url     : https://prove2.me/submissions/cf386ffb-41ac-4097-a52d-5996f1a38827

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
variable {E : Type} [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.InfAdeleCM
theorem _root_.solution [IsTotallyReal F] {σ σ' : F →+* ℂ} (h : InfinitePlace.mk σ = InfinitePlace.mk σ') : σ = σ' := by
  rw [← InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal σ), h,
    InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal σ')]
end GlobalTheory.InfAdeleCM

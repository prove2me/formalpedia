-- Prove2me | solution 1 for GlobalTheory.HeckeOne.extensionEmbedding_mixedSymm_of_isReal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:41.540476+00:00
-- url     : https://prove2.me/submissions/c6737a5c-4b5e-46e7-a365-a1cfb1e2e3ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HeckeLEntireAndNonzeroAtOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSmoothMulExtensionOfContinuousChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExtensionEmbeddingMixedSymmOfIsComplex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Classical
open scoped ContDiff
open Formalism.L2.Host (HChar)
open GlobalTheory.CMVal (Ideles)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleNorm)
open GlobalTheory GlobalTheory.HeckeOne
variable (K : Type) [Field K] [NumberField K]
namespace GlobalTheory.HeckeOne
theorem _root_.solution (y : mixedSpace K) (v : InfinitePlace K) (hv : v.IsReal) :
    InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y v) = y.1 ⟨v, hv⟩ :=
  congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply y)) ⟨v, hv⟩
end GlobalTheory.HeckeOne

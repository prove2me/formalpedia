-- Prove2me | solution 1 for GlobalTheory.HeckeOne.extensionEmbedding_mixedSymm_of_isComplex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:41.523591+00:00
-- url     : https://prove2.me/submissions/d9d605ec-9ba6-4c6d-92b4-bce8ec50e0dd

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
theorem _root_.solution (y : mixedSpace K) (v : InfinitePlace K) (hv : v.IsComplex) :
    InfinitePlace.Completion.extensionEmbedding v
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y v) = y.2 ⟨v, hv⟩ :=
  congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply y)) ⟨v, hv⟩
end GlobalTheory.HeckeOne

-- Prove2me | solution 1 for GlobalTheory.HeckeOne.mixedIdele_mixedEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:19:09.770897+00:00
-- url     : https://prove2.me/submissions/c2153f5a-ee1e-4090-bdad-855236f43f82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HeckeLEntireAndNonzeroAtOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSmoothMulExtensionOfContinuousChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExtensionEmbeddingMixedSymmOfIsComplex
import Theorems.Thm_GlobalTheory_CMVal_infDiag_eq


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
theorem _root_.solution (k : Kˣ) :
    mixedIdele K (Units.map (mixedEmbedding K).toMonoidHom k) = Formalism.L2.Host.infDiag k := by
  rw [GlobalTheory.CMVal.infDiag_eq]
  apply Units.ext
  apply Prod.ext
  · change (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (mixedEmbedding K (k : K)) = algebraMap K _ (k : K)
    rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, RingEquiv.symm_apply_apply]
  · rfl
end GlobalTheory.HeckeOne

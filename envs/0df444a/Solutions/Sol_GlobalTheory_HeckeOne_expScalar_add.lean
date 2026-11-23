-- Prove2me | solution 1 for GlobalTheory.HeckeOne.expScalar_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:53.8201+00:00
-- url     : https://prove2.me/submissions/b24e0f3e-ee97-40ba-a5f8-4d071e2b3736

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
theorem _root_.solution (x y : ℝ) : expScalar K (x + y) = expScalar K x * expScalar K y :=
  Units.ext (by
    change algebraMap ℝ (mixedSpace K) (Real.exp (x + y)) = algebraMap ℝ _ (Real.exp x) * algebraMap ℝ _ (Real.exp y)
    rw [Real.exp_add, map_mul])
end GlobalTheory.HeckeOne

-- Prove2me | solution 1 for GlobalTheory.HeckeOne.continuous_expScalar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:15.283923+00:00
-- url     : https://prove2.me/submissions/02d9b376-1911-4acc-85a7-fa1cea7f5b5f

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
theorem _root_.solution : Continuous (expScalar K) :=
  Units.continuous_iff.2 ⟨(continuous_algebraMap ℝ (mixedSpace K)).comp Real.continuous_exp,
    (continuous_algebraMap ℝ (mixedSpace K)).comp (Real.continuous_exp.comp continuous_neg)⟩
end GlobalTheory.HeckeOne

-- Prove2me | solution 1 for GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:14:05.87995+00:00
-- url     : https://prove2.me/submissions/078c7f22-9f8a-4f37-91d9-033557017e52

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Theorems.Thm_GlobalTheory_NormIntegers_isAdicComplete_of_fg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing
open scoped Matrix TensorProduct nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LocalLattice
noncomputable section
open GlobalTheory GlobalTheory.SelfDualGenus
variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
namespace GlobalTheory.SelfDualGenus
theorem _root_.solution :
    IsAdicComplete (maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K) := by
  refine NormIntegers.isAdicComplete_of_fg (C := v.adicCompletion K) ⟨?_, ?_, ?_⟩
    (IsNoetherian.noetherian _) (maximalIdeal.isMaximal _).ne_top
  · exact FaithfulSMul.algebraMap_injective _ _
  · intro x
    have : ‖(x : v.adicCompletion K)‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.2 x.2
    exact_mod_cast this
  · intro x hx
    have : ‖x‖ ≤ 1 := by exact_mod_cast hx
    exact ⟨⟨x, Valued.toNormedField.norm_le_one_iff.1 this⟩, rfl⟩
end GlobalTheory.SelfDualGenus

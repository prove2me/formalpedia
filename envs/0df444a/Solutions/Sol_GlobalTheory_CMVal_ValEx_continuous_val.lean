-- Prove2me | solution 1 for GlobalTheory.CMVal.ValEx.continuous_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:05:04.482567+00:00
-- url     : https://prove2.me/submissions/b182b197-f4fb-4def-a0c2-594fa6412695

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUnitaryCharOfOpenSubgroupAndHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped WithZero
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.ValEx
variable {E : Type} [Field E] [NumberField E]
open WithZeroTopology
namespace GlobalTheory.CMVal.ValEx
theorem _root_.solution (w : HeightOneSpectrum (𝓞 E)) : Continuous fun x : w.adicCompletion E => Valued.v x :=
  Valued.continuous_valuation_of_surjective (w.valuedAdicCompletion_surjective E)
end GlobalTheory.CMVal.ValEx

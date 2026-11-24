-- Prove2me | solution 1 for GlobalTheory.UnitLemma.SwapInt.conjO_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:00:15.294864+00:00
-- url     : https://prove2.me/submissions/e09db2f8-829a-4ef3-8394-980159ab2c91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralResidueComapInvolutionIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.SwapInt
namespace GlobalTheory.UnitLemma.SwapInt
theorem _root_.solution (K : UQ) (o : K.O) :
    algebraMap K.O K.E (conjO K o) = K.c (algebraMap K.O K.E o) :=
  (Classical.choose_spec (K.c_int o)).symm
end GlobalTheory.UnitLemma.SwapInt

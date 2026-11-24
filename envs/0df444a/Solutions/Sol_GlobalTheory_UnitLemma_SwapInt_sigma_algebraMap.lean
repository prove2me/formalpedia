-- Prove2me | solution 1 for GlobalTheory.UnitLemma.SwapInt.sigma_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:10:31.676275+00:00
-- url     : https://prove2.me/submissions/f346cc7f-500c-4ed8-96bb-82a626349523

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralResidueComapInvolutionIff
import Theorems.Thm_GlobalTheory_UnitLemma_SwapInt_conjO_spec

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
theorem _root_.solution {K : UQ} (B : InvAlg K) (o : K.O) :
    B.σ (algebraMap K.O B.A o) = algebraMap K.O B.A (conjO K o) := by
  rw [IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg, ← conjO_spec,
    ← IsScalarTower.algebraMap_apply K.O K.E B.A]
end GlobalTheory.UnitLemma.SwapInt

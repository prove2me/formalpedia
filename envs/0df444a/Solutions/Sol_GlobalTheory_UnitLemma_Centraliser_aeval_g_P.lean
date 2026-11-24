-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Centraliser.aeval_g_P
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:38:40.509372+00:00
-- url     : https://prove2.me/submissions/57e3bc86-560d-49ab-934e-1a99deeaba0b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_UniNilp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyDvdPowOfAevalEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Centraliser
namespace GlobalTheory.UnitLemma.Centraliser
theorem _root_.solution {K : UQ} (B : InvAlg K) : aeval B.g B.P = 0 := by
  have h := LinearMap.aeval_self_charpoly (LinearMap.mulLeft K.E B.g)
  have h' : Algebra.lmul K.E B.A (aeval B.g B.P) = 0 := by
    rw [← aeval_algHom_apply]; exact h
  simpa using congrArg (fun f : Module.End K.E B.A => f 1) h'
end GlobalTheory.UnitLemma.Centraliser

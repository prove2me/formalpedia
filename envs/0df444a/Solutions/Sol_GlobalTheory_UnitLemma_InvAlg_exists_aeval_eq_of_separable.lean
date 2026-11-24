-- Prove2me | solution 1 for GlobalTheory.UnitLemma.InvAlg.exists_aeval_eq_of_separable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:41:02.111334+00:00
-- url     : https://prove2.me/submissions/d42aea54-8050-4978-b92f-6a2b8ed0716d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CharpolyDvdPowFinrankOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfCharpolySeparableInvolution
import Theorems.Thm_GlobalTheory_UnitLemma_exists_aeval_eq_of_charpoly_separable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma
namespace GlobalTheory.UnitLemma
namespace InvAlg
theorem _root_.solution :
    ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ a : B.A, ∃ f : K.E[X], a = aeval B.g f :=
  fun _ B hP a => exists_aeval_eq_of_charpoly_separable B.g hP a
end InvAlg
end GlobalTheory.UnitLemma

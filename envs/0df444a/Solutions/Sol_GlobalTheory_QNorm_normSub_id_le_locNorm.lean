-- Prove2me | solution 1 for GlobalTheory.QNorm.normSub_id_le_locNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:58:56.493077+00:00
-- url     : https://prove2.me/submissions/8d650697-10bb-47aa-8342-a4952b56446b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FirstInequalitySUnitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TwoPowLeIndexLocalNormsSqrtExtensionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsSupUnitsLocalNormsSqrtNeTop
import Theorems.Thm_GlobalTheory_QNorm_normSub_id_le_normSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution (F : Type) [Field F] [NumberField F] (δ : F)
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    normSub (RingHom.id F) δ ≤ locNorm F δ S :=
  le_inf (le_iInf₂ fun _ _ => normSub_id_le_normSub _ δ)
    (le_iInf fun _ => normSub_id_le_normSub _ δ)
end GlobalTheory.QNorm

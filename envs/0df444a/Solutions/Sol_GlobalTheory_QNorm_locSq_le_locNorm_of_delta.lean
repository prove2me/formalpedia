-- Prove2me | solution 1 for GlobalTheory.QNorm.locSq_le_locNorm_of_delta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:43:45.144015+00:00
-- url     : https://prove2.me/submissions/02f7fb7f-5cd8-4075-a011-71a0b6744b44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TwoPowCardLeIndexIInfStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsApproxModLocalSquaresStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsLocalNonnormOfNonsquareAdicCompletionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexUnitsLocalSquaresFiniteRealPlacesLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TwoPowLeIndexLocalNormsSqrtExtension
import Theorems.Thm_GlobalTheory_QNorm_sqSub_le_normSub


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
    (S : Finset (HeightOneSpectrum (𝓞 F))) : locSq F S ≤ locNorm F δ S := by
  unfold locSq locNorm finSq
  exact inf_le_inf (iInf_mono fun v => iInf_mono fun _ => sqSub_le_normSub _ _)
    (iInf_mono fun σ => sqSub_le_normSub _ _)
end GlobalTheory.QNorm

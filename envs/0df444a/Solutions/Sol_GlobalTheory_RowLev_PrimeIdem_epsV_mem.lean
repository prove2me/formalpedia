-- Prove2me | solution 1 for GlobalTheory.RowLev.PrimeIdem.epsV_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:15:38.15489+00:00
-- url     : https://prove2.me/submissions/610cbde3-b04b-4352-a371-4a0ec6c5a619

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsAdicCompleteAndCardQuotientAdicCompletionInteg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPrimeIdempotentIntegralAdeles
import Theorems.Thm_GlobalTheory_RowLev_PrimeIdem_mem_map_of_apply_eq_zero
import Theorems.Thm_Formalism_UG_P_afsplitI_mem_intAd
import Theorems.Thm_Formalism_UG_P_afsplitI_ne


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
open GlobalTheory GlobalTheory.RowLev
open GlobalTheory.RowLev.PrimeIdem
open Formalism.UG Formalism.UG.P
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.RowLev.PrimeIdem
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (u : HeightOneSpectrum (𝓞 E)) (h : u.under (𝓞 F) ≠ v) :
    epsV E v ∈ u.asIdeal.map (Inhab.psi F E) :=
  mem_map_of_apply_eq_zero u (afsplitI v 1) (afsplitI_mem_intAd _ _ (one_mem _)) (afsplitI_ne v _ h 1) _ rfl
end GlobalTheory.RowLev.PrimeIdem

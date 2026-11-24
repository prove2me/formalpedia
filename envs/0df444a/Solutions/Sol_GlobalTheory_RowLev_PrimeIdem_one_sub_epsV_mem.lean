-- Prove2me | solution 1 for GlobalTheory.RowLev.PrimeIdem.one_sub_epsV_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:15:42.137482+00:00
-- url     : https://prove2.me/submissions/8f74986a-89b6-40ee-9621-1b24273e6604

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
import Theorems.Thm_Formalism_UG_P_afsplitI_self
import Theorems.Thm_Formalism_UG_P_afsplit_one_apply
import Theorems.Thm_Formalism_UG_P_afsplit_sub_apply


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
theorem _root_.solution (w : HeightOneSpectrum (𝓞 E)) :
    1 - epsV E (w.under (𝓞 F)) ∈ w.asIdeal.map (Inhab.psi F E) := by
  refine mem_map_of_apply_eq_zero w (1 - afsplitI (w.under (𝓞 F)) 1)
    (sub_mem (one_mem _) (afsplitI_mem_intAd _ _ (one_mem _))) ?_ _ ?_
  · rw [afsplit_sub_apply, afsplitI_self, afsplit_one_apply, sub_self]
  · rw [TensorProduct.tmul_sub]; rfl
end GlobalTheory.RowLev.PrimeIdem

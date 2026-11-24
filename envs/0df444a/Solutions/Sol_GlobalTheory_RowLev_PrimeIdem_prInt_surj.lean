-- Prove2me | solution 1 for GlobalTheory.RowLev.PrimeIdem.prInt_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:29:30.468804+00:00
-- url     : https://prove2.me/submissions/ff273e6b-13f6-4f98-b8f5-ce60030bc7fd

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsAdicCompleteAndCardQuotientAdicCompletionInteg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPrimeIdempotentIntegralAdeles
import Theorems.Thm_Formalism_UG_P_afsplit_IE_int
import Theorems.Thm_Formalism_UG_P_afsplit_prV_IE


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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) : Function.Surjective (prInt E v) := fun y =>
  ⟨⟨afsplitIE v y.1, afsplit_IE_int v y.1 y.2⟩, Subtype.ext (afsplit_prV_IE v y.1)⟩
end GlobalTheory.RowLev.PrimeIdem

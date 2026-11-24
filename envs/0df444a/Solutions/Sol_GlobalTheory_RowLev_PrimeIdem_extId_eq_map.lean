-- Prove2me | solution 1 for GlobalTheory.RowLev.PrimeIdem.extId_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:15:40.406517+00:00
-- url     : https://prove2.me/submissions/c5f44f48-540c-4529-992d-640157944d39

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsAdicCompleteAndCardQuotientAdicCompletionInteg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPrimeIdempotentIntegralAdeles

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
namespace GlobalTheory.RowLev.PrimeIdem
theorem _root_.solution (I : AutInst) (𝔞 : Ideal (𝓞 I.E)) : extId I 𝔞 = 𝔞.map (Inhab.psi I.F I.E) := by
  unfold extId Ideal.map
  congr 1
  ext z
  exact ⟨fun ⟨a, ha, e⟩ => ⟨a, ha, (Subtype.ext e).symm⟩, fun ⟨a, ha, e⟩ => ⟨a, ha, e ▸ rfl⟩⟩
end GlobalTheory.RowLev.PrimeIdem

-- Prove2me | solution 1 for GlobalTheory.RowLev.PrimeIdem.epsV_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:29:29.144446+00:00
-- url     : https://prove2.me/submissions/3b6cb66a-3f33-4ad9-97d9-f7f7ddbefc38

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsAdicCompleteAndCardQuotientAdicCompletionInteg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPrimeIdempotentIntegralAdeles
import Theorems.Thm_Formalism_UG_P_afsplit_decomp


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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) {x y : IntAf F E} (h : prInt E v x = prInt E v y) :
    epsV E v * x = epsV E v * y := by
  apply Subtype.ext
  have h' : prV (E := E) v x.1 = prV (E := E) v y.1 := congrArg Subtype.val h
  show afsplitEps E v * x.1 = afsplitEps E v * y.1
  rw [← afsplit_decomp, ← afsplit_decomp, h']
end GlobalTheory.RowLev.PrimeIdem

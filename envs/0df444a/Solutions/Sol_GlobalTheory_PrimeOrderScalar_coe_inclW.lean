-- Prove2me | solution 1 for GlobalTheory.PrimeOrderScalar.coe_inclW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:35:21.923957+00:00
-- url     : https://prove2.me/submissions/38a14093-4e14-4ea7-93af-53c04c09a294

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ActsBySameInteger

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix
open GlobalTheory GlobalTheory.PrimeOrderScalar
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.PrimeOrderScalar
theorem _root_.solution (w : HeightOneSpectrum (𝓞 F)) (y : w.adicCompletionIntegers F) :
    ((inclW (E := E) w y : intV E w) : E ⊗[F] w.adicCompletion F) = (1 : E) ⊗ₜ (y : w.adicCompletion F) :=
  rfl
end GlobalTheory.PrimeOrderScalar

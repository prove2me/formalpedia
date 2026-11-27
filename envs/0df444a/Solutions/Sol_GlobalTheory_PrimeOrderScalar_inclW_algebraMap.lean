-- Prove2me | solution 1 for GlobalTheory.PrimeOrderScalar.inclW_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:39:39.479836+00:00
-- url     : https://prove2.me/submissions/eeb9c94a-c598-446a-8fc3-46c8d6223be4

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ActsBySameInteger
import Theorems.Thm_GlobalTheory_PrimeOrderScalar_coe_inclW

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
theorem _root_.solution (w : HeightOneSpectrum (𝓞 F)) (d : 𝓞 F) :
    ((inclW (E := E) w (algebraMap (𝓞 F) (w.adicCompletionIntegers F) d) : intV E w) :
      E ⊗[F] w.adicCompletion F) = algebraMap F E (d : F) ⊗ₜ (1 : w.adicCompletion F) := by
  rw [coe_inclW, ← Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply']
  rfl
end GlobalTheory.PrimeOrderScalar

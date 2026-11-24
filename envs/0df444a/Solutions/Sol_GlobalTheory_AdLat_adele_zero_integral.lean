-- Prove2me | solution 1 for GlobalTheory.AdLat.adele_zero_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:54:15.70414+00:00
-- url     : https://prove2.me/submissions/0362cb76-8d0e-4a28-97d2-e2d26037a57e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.AdLat
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) :
    (0 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F := by
  have : (0 : FiniteAdeleRing (𝓞 F) F) v = 0 := RestrictedProduct.zero_apply _ _
  rw [this]; exact zero_mem _
end GlobalTheory.AdLat
